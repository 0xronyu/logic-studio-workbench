(() => {
  'use strict';

  const $ = (selector) => document.querySelector(selector);
  const expressionInput = $('#expressionInput');
  const domainInput = $('#domainInput');
  const diagram = $('#diagram');
  const truthContent = $('#truthContent');
  const annotations = new Map();
  let currentAst = null;
  let currentDomain = ['a', 'b'];
  let selectedPath = 'root';
  let toastTimer;

  const OP = {
    '.': {name: 'AND', label: '逻辑与', symbol: '∧', arity: 2, type: 'operator'},
    ',': {name: 'OR', label: '逻辑或', symbol: '∨', arity: 2, type: 'operator'},
    '<': {name: 'NOT', label: '逻辑非', symbol: '¬', arity: 1, type: 'operator'},
    '>': {name: 'IMPLIES', label: '逻辑推出', symbol: '→', arity: 2, type: 'operator'},
    '=': {name: 'EQUIV', label: '逻辑等价', symbol: '↔', arity: 2, type: 'operator'}
  };

  function tokenize(source) {
    const tokenPattern = /[∀∃]\s*[A-Za-z_][A-Za-z0-9_]*|[A-Za-z_][A-Za-z0-9_]*(?:\([A-Za-z_][A-Za-z0-9_]*\))?|[01]|[.,<>=]/g;
    const tokens = [];
    let lastIndex = 0;
    for (const match of source.matchAll(tokenPattern)) {
      const gap = source.slice(lastIndex, match.index);
      if (/\S/.test(gap)) throw new Error(`无法识别“${gap.trim()}”。谓词请写成 P(x)，量词请写成 ∀x 或 ∃x。`);
      tokens.push(match[0].replace(/\s+/g, ''));
      lastIndex = match.index + match[0].length;
    }
    const tail = source.slice(lastIndex);
    if (/\S/.test(tail)) throw new Error(`表达式末尾存在无法识别的内容：“${tail.trim()}”。`);
    if (!tokens.length) throw new Error('请先输入一个逆波兰逻辑表达式。');
    return tokens;
  }

  function parseRpn(source) {
    const tokens = tokenize(source);
    const stack = [];
    for (const token of tokens) {
      if (Object.hasOwn(OP, token)) {
        const meta = OP[token];
        if (stack.length < meta.arity) {
          throw new Error(`操作符“${token}”需要 ${meta.arity} 个操作数，当前只找到 ${stack.length} 个。`);
        }
        const right = stack.pop();
        const left = meta.arity === 2 ? stack.pop() : null;
        stack.push({type: 'operator', op: token, left, right});
        continue;
      }
      const quantifier = token.match(/^([∀∃])([A-Za-z_][A-Za-z0-9_]*)$/);
      if (quantifier) {
        if (!stack.length) throw new Error(`量词“${token}”前面没有可限定的子式。`);
        stack.push({type: 'quantifier', quantifier: quantifier[1], variable: quantifier[2], child: stack.pop()});
        continue;
      }
      if (/^[01]$/.test(token) || /^[A-Za-z_][A-Za-z0-9_]*(?:\([A-Za-z_][A-Za-z0-9_]*\))?$/.test(token)) {
        stack.push({type: token === '0' || token === '1' ? 'constant' : 'atom', value: token});
        continue;
      }
      throw new Error(`未知符號：${token}`);
    }
    if (stack.length !== 1) {
      throw new Error(stack.length > 1
        ? `表达式还剩 ${stack.length} 个未组合的子式；请检查操作符或量词的位置。`
        : '表达式没有形成完整公式。');
    }
    return {ast: stack[0], tokens};
  }

  function parseDomain(raw) {
    const values = raw.split(',').map((value) => value.trim()).filter(Boolean);
    if (!values.length) throw new Error('论域不能为空，请至少输入一个元素。');
    if (values.length > 4) throw new Error('为了让真值表保持清晰，论域最多支持 4 个元素。');
    if (values.some((value) => !/^[A-Za-z_][A-Za-z0-9_]*$/.test(value))) {
      throw new Error('论域元素请使用字母、数字或下划线，元素之间以逗号分隔。');
    }
    if (new Set(values).size !== values.length) throw new Error('论域元素不能重复。');
    return values;
  }

  function substitute(value, environment) {
    let output = value;
    for (const [variable, replacement] of environment) {
      const pattern = new RegExp(`\\b${variable.replace(/[.*+?^${}()|[\\]\\]/g, '\\$&')}\\b`, 'g');
      output = output.replace(pattern, replacement);
    }
    return output;
  }

  function collectAtoms(node, domain, environment = new Map(), found = new Set()) {
    if (node.type === 'atom') {
      found.add(substitute(node.value, environment));
    } else if (node.type === 'operator') {
      if (node.left) collectAtoms(node.left, domain, environment, found);
      collectAtoms(node.right, domain, environment, found);
    } else if (node.type === 'quantifier') {
      for (const element of domain) {
        const next = new Map(environment);
        next.set(node.variable, element);
        collectAtoms(node.child, domain, next, found);
      }
    }
    return found;
  }

  function evaluate(node, assignment, domain, environment = new Map()) {
    if (node.type === 'constant') return node.value === '1';
    if (node.type === 'atom') return Boolean(assignment[substitute(node.value, environment)]);
    if (node.type === 'quantifier') {
      const outcomes = domain.map((element) => {
        const next = new Map(environment);
        next.set(node.variable, element);
        return evaluate(node.child, assignment, domain, next);
      });
      return node.quantifier === '∀' ? outcomes.every(Boolean) : outcomes.some(Boolean);
    }
    const left = node.left ? evaluate(node.left, assignment, domain, environment) : null;
    const right = evaluate(node.right, assignment, domain, environment);
    switch (node.op) {
      case '.': return left && right;
      case ',': return left || right;
      case '<': return !right;
      case '>': return !left || right;
      case '=': return left === right;
      default: throw new Error(`不支持的操作符：${node.op}`);
    }
  }

  function pretty(node) {
    if (node.type === 'constant' || node.type === 'atom') return node.value;
    if (node.type === 'quantifier') return `${node.quantifier}${node.variable} ${pretty(node.child)}`;
    const op = OP[node.op];
    if (node.op === '<') return `¬(${pretty(node.right)})`;
    return `(${pretty(node.left)} ${op.symbol} ${pretty(node.right)})`;
  }

  function countNodes(node) {
    if (node.type === 'atom' || node.type === 'constant') return 1;
    if (node.type === 'quantifier') return 1 + countNodes(node.child);
    return 1 + (node.left ? countNodes(node.left) : 0) + countNodes(node.right);
  }

  function getNodeAtPath(node, path) {
    if (path === 'root') return node;
    const parts = path.split('.').slice(1);
    let current = node;
    for (const part of parts) {
      if (!current) return null;
      if (current.type === 'quantifier') current = current.child;
      else if (part === '0') current = current.left;
      else current = current.right;
    }
    return current;
  }

  function nodeChildren(node, path) {
    if (node.type === 'quantifier') return [{node: node.child, path: `${path}.0`}];
    if (node.type === 'operator') {
      if (node.op === '<') return [{node: node.right, path: `${path}.0`}];
      return [{node: node.left, path: `${path}.0`}, {node: node.right, path: `${path}.1`}];
    }
    return [];
  }

  function nodeTitle(node) {
    if (node.type === 'quantifier') return node.quantifier === '∀' ? '全称量词' : '存在量词';
    if (node.type === 'operator') return OP[node.op].label;
    return node.type === 'constant' ? '逻辑常量' : '命题 / 谓词';
  }

  function nodeExpression(node) {
    if (node.type === 'quantifier') return `${node.quantifier}${node.variable}`;
    if (node.type === 'operator') return OP[node.op].symbol;
    return node.value;
  }

  function nodeClass(node) {
    if (node.type === 'quantifier') return 'quantifier';
    if (node.type === 'operator') return 'operator';
    if (node.type === 'constant') return 'constant';
    return 'atom';
  }

  function drawTree() {
    diagram.replaceChildren();
    const render = (node, path) => {
      const branch = document.createElement('div');
      branch.className = 'tree-branch';
      const button = document.createElement('button');
      button.type = 'button';
      button.className = `tree-node ${nodeClass(node)}${selectedPath === path ? ' selected' : ''}`;
      button.setAttribute('aria-label', `${nodeTitle(node)} ${nodeExpression(node)}`);
      const kind = document.createElement('span');
      kind.className = 'node-kind';
      kind.textContent = annotations.get(path)?.name || nodeTitle(node);
      const main = document.createElement('span');
      main.className = 'node-main';
      main.textContent = nodeExpression(node);
      button.append(kind, main);
      const memo = annotations.get(path)?.memo;
      if (memo) {
        const note = document.createElement('span');
        note.className = 'node-annotation';
        note.textContent = memo;
        button.append(note);
      }
      button.addEventListener('click', () => selectNode(path));
      branch.append(button);
      const children = nodeChildren(node, path);
      if (children.length) {
        const container = document.createElement('div');
        container.className = 'tree-children';
        for (const item of children) {
          const childWrap = document.createElement('div');
          childWrap.className = 'tree-child-wrap';
          childWrap.append(render(item.node, item.path));
          container.append(childWrap);
        }
        branch.append(container);
      }
      return branch;
    };
    diagram.append(render(currentAst, 'root'));
  }

  function selectNode(path) {
    selectedPath = path;
    const node = getNodeAtPath(currentAst, path);
    if (!node) return;
    const note = annotations.get(path) || {};
    $('#selectedType').textContent = nodeTitle(node);
    $('#selectedPath').textContent = path;
    $('#selectedFormula').textContent = nodeExpression(node);
    $('#annotationName').value = note.name || '';
    $('#annotationMemo').value = note.memo || '';
    drawTree();
  }

  function renderTruthTable(ast, domain) {
    const atoms = [...collectAtoms(ast, domain)].sort((a, b) => a.localeCompare(b));
    $('#atomMetric').textContent = String(atoms.length);
    $('#domainMetric').textContent = String(domain.length);
    if (atoms.length > 8) {
      $('#truthSummary').textContent = '变量过多';
      truthContent.replaceChildren();
      const message = document.createElement('p');
      message.className = 'truth-explanation';
      message.innerHTML = `当前公式展开后有 <strong>${atoms.length} 个原子项</strong>。真值表为避免生成过大的表格，最多支持 8 个原子项（256 行）；公式树仍可正常查看。`;
      truthContent.append(message);
      return;
    }
    const rowCount = 2 ** atoms.length;
    $('#truthSummary').textContent = `${rowCount} 种赋值`;
    const wrapper = document.createElement('div');
    wrapper.className = 'truth-table-scroll';
    const table = document.createElement('table');
    table.className = 'truth-table';
    const thead = document.createElement('thead');
    const headerRow = document.createElement('tr');
    for (const atom of atoms) {
      const th = document.createElement('th');
      th.scope = 'col';
      th.textContent = atom;
      headerRow.append(th);
    }
    const resultHead = document.createElement('th');
    resultHead.scope = 'col';
    resultHead.className = 'result-th';
    resultHead.textContent = '结果';
    headerRow.append(resultHead);
    thead.append(headerRow);
    const tbody = document.createElement('tbody');
    let trueCount = 0;
    for (let row = 0; row < rowCount; row += 1) {
      const assignment = {};
      atoms.forEach((atom, index) => { assignment[atom] = Boolean(row & (1 << (atoms.length - 1 - index))); });
      const result = evaluate(ast, assignment, domain);
      if (result) trueCount += 1;
      const tr = document.createElement('tr');
      for (const atom of atoms) {
        const td = document.createElement('td');
        td.append(truthBadge(assignment[atom]));
        tr.append(td);
      }
      const resultTd = document.createElement('td');
      resultTd.className = 'result-cell';
      resultTd.append(truthBadge(result));
      tr.append(resultTd);
      tbody.append(tr);
    }
    table.append(thead, tbody);
    wrapper.append(table);
    truthContent.replaceChildren(wrapper);
    const hint = document.createElement('p');
    hint.className = 'truth-hint';
    hint.textContent = `${rowCount} 行赋值 · ${trueCount} 行结果为真${atoms.length ? ' · T=真，F=假' : ''}`;
    truthContent.append(hint);
  }

  function truthBadge(value) {
    const badge = document.createElement('span');
    badge.className = `truth-cell ${value ? 'truth-true' : 'truth-false'}`;
    badge.textContent = value ? 'T' : 'F';
    badge.setAttribute('aria-label', value ? '真' : '假');
    return badge;
  }

  function analyze({persist = true} = {}) {
    try {
      const domain = parseDomain(domainInput.value);
      const parsed = parseRpn(expressionInput.value);
      currentAst = parsed.ast;
      currentDomain = domain;
      selectedPath = 'root';
      if (persist) {
        try { localStorage.setItem('logic-studio-v2', JSON.stringify({expression: expressionInput.value, domain: domain.join(',')})); } catch (_) { /* Storage is optional. */ }
      }
      $('#formulaPreview').textContent = pretty(currentAst);
      const nodes = countNodes(currentAst);
      $('#formulaComplexity').textContent = `${nodes} 个节点`;
      $('#nodeCount').textContent = String(nodes).padStart(2, '0');
      const quantifiers = countQuantifiers(currentAst);
      $('#quantifierMetric').textContent = String(quantifiers);
      $('#logicTypeMetric').textContent = quantifiers ? '谓词逻辑' : '命题逻辑';
      const atoms = [...collectAtoms(currentAst, domain)];
      $('#resultTitle').textContent = quantifiers ? '有限模型已分析' : '真值表已生成';
      $('#resultDescription').textContent = quantifiers
        ? `量词已在 ${domain.length} 元素的有限论域中展开。`
        : '所有原子命题组合均已计算。';
      drawTree();
      selectNode('root');
      renderTruthTable(currentAst, domain);
      updateTokenCount(parsed.tokens.length);
      setToast('表达式分析完成');
      return true;
    } catch (error) {
      currentAst = null;
      diagram.replaceChildren();
      truthContent.replaceChildren();
      const message = document.createElement('p');
      message.className = 'truth-explanation error';
      message.textContent = error.message;
      truthContent.append(message);
      $('#formulaPreview').textContent = '表达式需要检查';
      $('#formulaComplexity').textContent = '解析失败';
      $('#truthSummary').textContent = '无法分析';
      $('#resultTitle').textContent = '请检查表达式';
      $('#resultDescription').textContent = error.message;
      setToast(error.message, true);
      return false;
    }
  }

  function countQuantifiers(node) {
    if (node.type === 'quantifier') return 1 + countQuantifiers(node.child);
    if (node.type === 'operator') return (node.left ? countQuantifiers(node.left) : 0) + countQuantifiers(node.right);
    return 0;
  }

  function updateTokenCount(count) {
    $('#tokenCount').textContent = `${count} 个符号`;
  }

  function setToast(message, isError = false) {
    const toast = $('#toast');
    toast.textContent = message;
    toast.style.background = isError ? '#873f44' : '';
    toast.classList.add('show');
    clearTimeout(toastTimer);
    toastTimer = setTimeout(() => toast.classList.remove('show'), 2200);
  }

  function download(filename, content, mimeType) {
    const blob = new Blob([content], {type: mimeType});
    const url = URL.createObjectURL(blob);
    const link = document.createElement('a');
    link.href = url;
    link.download = filename;
    link.click();
    setTimeout(() => URL.revokeObjectURL(url), 1000);
  }

  function exportJson() {
    if (!currentAst && !analyze()) return;
    const project = {
      format: 'LogicStudioProject',
      version: 2,
      sourceExpression: expressionInput.value.trim(),
      domain: currentDomain,
      annotations: Object.fromEntries(annotations),
      exportedAt: new Date().toISOString()
    };
    download('logic-studio-project.json', JSON.stringify(project, null, 2), 'application/json;charset=utf-8');
    setToast('项目 JSON 已导出');
  }

  function exportText() {
    if (!expressionInput.value.trim()) return setToast('没有可导出的表达式', true);
    download('logic-expression.txt', `${expressionInput.value.trim()}\n`, 'text/plain;charset=utf-8');
    setToast('表达式文本已导出');
  }

  async function importFile(file) {
    try {
      const text = await file.text();
      if (file.name.toLowerCase().endsWith('.json')) {
        const project = JSON.parse(text);
        if (project.format !== 'LogicStudioProject' || typeof project.sourceExpression !== 'string') {
          throw new Error('无法识别此 JSON 项目文件；请导入 Logic Studio 导出的项目。');
        }
        expressionInput.value = project.sourceExpression;
        domainInput.value = Array.isArray(project.domain) ? project.domain.join(',') : 'a,b';
        annotations.clear();
        if (project.annotations && typeof project.annotations === 'object') {
          for (const [path, annotation] of Object.entries(project.annotations)) {
            if (annotation && typeof annotation === 'object') annotations.set(path, {name: String(annotation.name || ''), memo: String(annotation.memo || '')});
          }
        }
        analyze();
        setToast('项目已载入');
      } else {
        expressionInput.value = text.trim();
        analyze();
      }
    } catch (error) {
      setToast(error.message || '文件无法读取', true);
    }
  }

  function copyTruthTable() {
    if (!currentAst) return setToast('先分析一个表达式', true);
    const atoms = [...collectAtoms(currentAst, currentDomain)].sort((a, b) => a.localeCompare(b));
    if (atoms.length > 8) return setToast('变量超过真值表上限，暂不可复制', true);
    const lines = [[...atoms, '结果'].join('\t')];
    for (let row = 0; row < 2 ** atoms.length; row += 1) {
      const assignment = {};
      atoms.forEach((atom, index) => { assignment[atom] = Boolean(row & (1 << (atoms.length - 1 - index))); });
      lines.push([...atoms.map((atom) => assignment[atom] ? '真' : '假'), evaluate(currentAst, assignment, currentDomain) ? '真' : '假'].join('\t'));
    }
    const text = lines.join('\n');
    if (navigator.clipboard?.writeText) {
      navigator.clipboard.writeText(text).then(() => setToast('真值表已复制')).catch(() => download('truth-table.tsv', text, 'text/tab-separated-values;charset=utf-8'));
    } else {
      download('truth-table.tsv', text, 'text/tab-separated-values;charset=utf-8');
      setToast('已下载真值表 TSV');
    }
  }

  $('#analyzeButton').addEventListener('click', () => analyze());
  $('#expressionInput').addEventListener('input', () => {
    const count = (expressionInput.value.match(/\S+/g) || []).length;
    updateTokenCount(count);
    document.querySelectorAll('.sample-card').forEach((card) => card.classList.toggle('selected', card.dataset.expression === expressionInput.value.trim()));
  });
  $('#domainInput').addEventListener('keydown', (event) => { if (event.key === 'Enter') analyze(); });
  $('#expressionInput').addEventListener('keydown', (event) => {
    if ((event.metaKey || event.ctrlKey) && event.key === 'Enter') { event.preventDefault(); analyze(); }
  });
  document.querySelectorAll('.sample-card').forEach((card) => card.addEventListener('click', () => {
    expressionInput.value = card.dataset.expression;
    domainInput.value = card.dataset.domain;
    document.querySelectorAll('.sample-card').forEach((item) => item.classList.toggle('selected', item === card));
    analyze();
  }));
  $('#resetButton').addEventListener('click', () => {
    expressionInput.value = 'P(x) Q(x) > ∀x';
    domainInput.value = 'a,b';
    annotations.clear();
    document.querySelectorAll('.sample-card').forEach((card) => card.classList.toggle('selected', card.dataset.expression === expressionInput.value));
    analyze();
  });
  $('#saveAnnotationButton').addEventListener('click', () => {
    if (!currentAst) return setToast('先分析一个表达式', true);
    const name = $('#annotationName').value.trim();
    const memo = $('#annotationMemo').value.trim();
    if (name || memo) annotations.set(selectedPath, {name, memo});
    else annotations.delete(selectedPath);
    drawTree();
    setToast('节点标注已保存');
  });
  $('#loadFileButton').addEventListener('click', () => $('#fileInput').click());
  $('#fileInput').addEventListener('change', (event) => {
    const [file] = event.target.files || [];
    if (file) importFile(file);
    event.target.value = '';
  });
  $('#exportJsonButton').addEventListener('click', exportJson);
  $('#exportTextButton').addEventListener('click', exportText);
  $('#copyTruthButton').addEventListener('click', copyTruthTable);
  $('#fitDiagramButton').addEventListener('click', () => {
    $('#diagramViewport').scrollTo({left: 0, top: 0, behavior: 'smooth'});
    setToast('已将公式树居中');
  });

  try {
    const previous = JSON.parse(localStorage.getItem('logic-studio-v2') || 'null');
    if (previous && typeof previous.expression === 'string') {
      expressionInput.value = previous.expression;
      domainInput.value = previous.domain || 'a,b';
    }
  } catch (_) { /* A malformed optional cache should not block the app. */ }
  updateTokenCount((expressionInput.value.match(/\S+/g) || []).length);
  analyze({persist: false});
})();
