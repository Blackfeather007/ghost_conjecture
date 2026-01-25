// 全局状态
let currentData = null;
let currentFileName = '';
let selectedItemIndex = null;
let filteredItems = [];
let currentView = 'list'; // 'list' or 'graph'
let network = null; // vis.js network instance
let graphData = null; // graph data structure

// DOM元素
const fileInput = document.getElementById('file-input');
const exportBtn = document.getElementById('export-btn');
const fileNameSpan = document.getElementById('file-name');
const viewToggleBtn = document.getElementById('view-toggle-btn');
const mainContent = document.getElementById('main-content');
const listView = document.getElementById('list-view');
const graphView = document.getElementById('graph-view');
const itemsList = document.getElementById('items-list');
const itemsCount = document.getElementById('items-count');
const filterSection = document.getElementById('filter-section');
const searchInput = document.getElementById('search-input');
const noSelection = document.getElementById('no-selection');
const itemDetail = document.getElementById('item-detail');
const saveBtn = document.getElementById('save-btn');
const graphContainer = document.getElementById('graph-container');
const graphLayoutSelect = document.getElementById('graph-layout');
const graphResetBtn = document.getElementById('graph-reset-btn');
const graphFitBtn = document.getElementById('graph-fit-btn');
const graphContentPanel = document.getElementById('graph-content-panel');
const graphContentTitle = document.getElementById('graph-content-title');
const graphContentBody = document.getElementById('graph-content-body');
const graphContentClose = document.getElementById('graph-content-close');

// 确保所有必需的DOM元素都存在
if (!graphContainer || !graphLayoutSelect || !graphResetBtn || !graphFitBtn) {
    console.error('图视图所需的DOM元素未找到');
}

// 详情面板元素
const detailType = document.getElementById('detail-type');
const detailLabel = document.getElementById('detail-label');
const detailSection = document.getElementById('detail-section');
const detailSubsection = document.getElementById('detail-subsection');
const detailLineNumber = document.getElementById('detail-line-number');
const detailContent = document.getElementById('detail-content');
const detailProof = document.getElementById('detail-proof');
const detailComment = document.getElementById('detail-comment');
const contentPreview = document.getElementById('content-preview');
const proofPreview = document.getElementById('proof-preview');
const dependenciesList = document.getElementById('dependencies-list');
const dependencySelect = document.getElementById('dependency-select');
const addDependencyBtn = document.getElementById('add-dependency-btn');

// 初始化
document.addEventListener('DOMContentLoaded', () => {
    setupEventListeners();
    
    // 等待KaTeX加载完成
    const checkKaTeX = setInterval(() => {
        if (typeof renderMathInElement !== 'undefined') {
            console.log('KaTeX已加载');
            clearInterval(checkKaTeX);
        }
    }, 100);
    
    // 10秒后停止检查
    setTimeout(() => {
        clearInterval(checkKaTeX);
        if (typeof renderMathInElement === 'undefined') {
            console.warn('KaTeX加载超时，LaTeX渲染可能不可用');
        }
    }, 10000);
});

// 设置事件监听器
function setupEventListeners() {
    fileInput.addEventListener('change', handleFileSelect);
    exportBtn.addEventListener('click', handleExport);
    viewToggleBtn.addEventListener('click', toggleView);
    // 类型筛选改为checkbox，需要监听所有checkbox的变化
    document.addEventListener('change', function(e) {
        if (e.target.classList.contains('filter-type-checkbox')) {
            handleTypeFilterChange(e);
        }
    });
    filterSection.addEventListener('change', applyFilters);
    searchInput.addEventListener('input', applyFilters);
    saveBtn.addEventListener('click', saveCurrentItem);
    detailContent.addEventListener('input', () => updateLaTeXPreview('content'));
    detailProof.addEventListener('input', () => updateLaTeXPreview('proof'));
    addDependencyBtn.addEventListener('click', addDependency);
    graphLayoutSelect.addEventListener('change', updateGraphLayout);
    // 图视图类型筛选改为checkbox，需要监听所有checkbox的变化
    document.addEventListener('change', function(e) {
        if (e.target.classList.contains('graph-filter-type-checkbox')) {
            handleGraphTypeFilterChange(e);
        }
    });
    graphResetBtn.addEventListener('click', resetGraphView);
    graphFitBtn.addEventListener('click', fitGraphView);
    graphContentClose.addEventListener('click', () => {
        graphContentPanel.style.display = 'none';
    });
}

// 处理文件选择
function handleFileSelect(event) {
    const file = event.target.files[0];
    if (!file) return;

    const reader = new FileReader();
    reader.onload = (e) => {
        try {
            const jsonData = JSON.parse(e.target.result);
            loadData(jsonData, file.name);
        } catch (error) {
            console.error('文件加载错误:', error);
            alert('文件格式错误: ' + error.message + '\n\n如果问题持续，请尝试：\n1. 清除浏览器缓存\n2. 硬刷新页面 (Ctrl+Shift+R 或 Cmd+Shift+R)');
        }
    };
    reader.onerror = (e) => {
        console.error('文件读取错误:', e);
        alert('文件读取失败，请重试');
    };
    reader.readAsText(file);
}

// 加载数据
function loadData(data, fileName) {
    currentData = data;
    currentFileName = fileName;
    
    // 确保每个条目都有dependencies和comment字段
    if (currentData.extracted_items) {
        currentData.extracted_items.forEach(item => {
            if (!item.hasOwnProperty('dependencies')) {
                item.dependencies = [];
            }
            if (!item.hasOwnProperty('comment')) {
                item.comment = '';
            }
        });
    }
    
    fileNameSpan.textContent = `当前文件: ${fileName}`;
    mainContent.style.display = 'block';
    exportBtn.disabled = false;
    viewToggleBtn.disabled = false;
    
    populateFilters();
    populateGraphFilters();
    applyFilters();
    buildGraphData();
}

// 填充筛选器选项
function populateFilters() {
    if (!currentData || !currentData.extracted_items) return;
    
    const types = new Set();
    const sections = new Set();
    
    currentData.extracted_items.forEach(item => {
        if (item.type) types.add(item.type);
        if (item.section) sections.add(item.section);
    });
    
    // 填充类型筛选器（多选checkbox）
    const filterTypeCheckboxes = document.getElementById('filter-type-checkboxes');
    filterTypeCheckboxes.innerHTML = `
        <label class="checkbox-label">
            <input type="checkbox" class="filter-type-checkbox" value="" checked>
            <span>全部</span>
        </label>
    `;
    Array.from(types).sort().forEach(type => {
        const label = document.createElement('label');
        label.className = 'checkbox-label';
        const checkbox = document.createElement('input');
        checkbox.type = 'checkbox';
        checkbox.className = 'filter-type-checkbox';
        checkbox.value = type;
        checkbox.checked = true; // 默认全选
        const span = document.createElement('span');
        span.textContent = type;
        label.appendChild(checkbox);
        label.appendChild(span);
        filterTypeCheckboxes.appendChild(label);
    });
    
    // 填充章节筛选器
    filterSection.innerHTML = '<option value="">全部</option>';
    Array.from(sections).sort().forEach(section => {
        const option = document.createElement('option');
        option.value = section;
        option.textContent = section;
        filterSection.appendChild(option);
    });
}

// 应用筛选
function applyFilters() {
    if (!currentData || !currentData.extracted_items) return;
    
    // 获取选中的类型（多选）
    const selectedTypes = Array.from(document.querySelectorAll('.filter-type-checkbox:checked'))
        .map(cb => cb.value)
        .filter(v => v !== ''); // 排除"全部"选项
    
    const allTypesSelected = document.querySelector('.filter-type-checkbox[value=""]')?.checked || false;
    const sectionFilter = filterSection.value;
    const searchTerm = searchInput.value.toLowerCase();
    
    filteredItems = currentData.extracted_items.filter((item, index) => {
        // 类型筛选：如果"全部"选中或该类型在选中列表中
        if (!allTypesSelected && selectedTypes.length > 0) {
            if (!selectedTypes.includes(item.type)) return false;
        }
        if (sectionFilter && item.section !== sectionFilter) return false;
        if (searchTerm) {
            const searchableText = [
                item.label || '',
                item.content || '',
                item.section || '',
                item.comment || ''
            ].join(' ').toLowerCase();
            if (!searchableText.includes(searchTerm)) return false;
        }
        return true;
    });
    
    displayItems();
}

// 显示条目列表
function displayItems() {
    itemsList.innerHTML = '';
    itemsCount.textContent = `(${filteredItems.length})`;
    
    if (filteredItems.length === 0) {
        itemsList.innerHTML = '<p style="text-align: center; color: #95a5a6; padding: 20px;">没有找到匹配的条目</p>';
        return;
    }
    
    filteredItems.forEach((item, displayIndex) => {
        const originalIndex = currentData.extracted_items.indexOf(item);
        const card = createItemCard(item, originalIndex, displayIndex);
        itemsList.appendChild(card);
    });
}

// 创建条目卡片
function createItemCard(item, originalIndex, displayIndex) {
    const card = document.createElement('div');
    card.className = 'item-card';
    if (selectedItemIndex === originalIndex) {
        card.classList.add('active');
    }
    
    const preview = item.content ? 
        item.content.replace(/\\[a-zA-Z]+\{([^}]*)\}/g, '$1').substring(0, 100) : 
        '(无内容)';
    
    // 计算有效的依赖数量（排除无效的依赖）
    let validDepsCount = 0;
    if (item.dependencies && item.dependencies.length > 0) {
        validDepsCount = item.dependencies.filter(dep => {
            if (typeof dep === 'string') {
                return findItemIndexByLabel(dep) >= 0;
            } else if (typeof dep === 'number') {
                return dep >= 0 && dep < currentData.extracted_items.length;
            }
            return false;
        }).length;
    }
    
    card.innerHTML = `
        <div class="item-card-header">
            <span class="item-type ${item.type || 'default'}">${item.type || 'unknown'}</span>
            ${item.label ? `<span class="item-label">${item.label}</span>` : ''}
        </div>
        <div class="item-preview">${escapeHtml(preview)}${item.content && item.content.length > 100 ? '...' : ''}</div>
        ${item.section ? `<div class="item-section">${escapeHtml(item.section)}</div>` : ''}
        ${validDepsCount > 0 ? 
            `<div class="item-section" style="color: #3498db;">依赖: ${validDepsCount} 项</div>` : ''}
    `;
    
    card.addEventListener('click', () => selectItem(originalIndex));
    
    return card;
}

// 选择条目
function selectItem(index) {
    selectedItemIndex = index;
    const item = currentData.extracted_items[index];
    
    // 更新列表中的活动状态
    document.querySelectorAll('.item-card').forEach(card => {
        card.classList.remove('active');
    });
    const cards = document.querySelectorAll('.item-card');
    const displayIndex = filteredItems.findIndex(i => currentData.extracted_items.indexOf(i) === index);
    if (displayIndex >= 0 && cards[displayIndex]) {
        cards[displayIndex].classList.add('active');
    }
    
    // 显示详情
    noSelection.style.display = 'none';
    itemDetail.style.display = 'block';
    
    // 填充详情
    detailType.value = item.type || '';
    detailLabel.value = item.label || '';
    detailSection.value = item.section || '';
    detailSubsection.value = item.subsection || '';
    detailLineNumber.value = item.line_number || '';
    detailContent.value = item.content || '';
    detailProof.value = item.proof || '';
    detailComment.value = item.comment || '';
    
    // 更新LaTeX预览
    updateLaTeXPreview('content');
    updateLaTeXPreview('proof');
    
    // 更新依赖关系
    updateDependencies();
    updateDependencySelect();
}

// 更新LaTeX预览
function updateLaTeXPreview(type) {
    const textarea = type === 'content' ? detailContent : detailProof;
    const previewDiv = type === 'content' ? contentPreview : proofPreview;
    const text = textarea.value;
    
    if (!text.trim()) {
        previewDiv.innerHTML = '';
        return;
    }
    
    // 转义HTML，然后渲染LaTeX
    const escapedText = escapeHtml(text);
    previewDiv.innerHTML = escapedText;
    
    // 使用KaTeX渲染数学公式
    if (typeof renderMathInElement !== 'undefined') {
        try {
            renderMathInElement(previewDiv, {
                delimiters: [
                    {left: '$$', right: '$$', display: true},
                    {left: '$', right: '$', display: false},
                    {left: '\\[', right: '\\]', display: true},
                    {left: '\\(', right: '\\)', display: false},
                    {left: '\\begin{equation}', right: '\\end{equation}', display: true},
                    {left: '\\begin{equation*}', right: '\\end{equation*}', display: true},
                    {left: '\\begin{align}', right: '\\end{align}', display: true},
                    {left: '\\begin{align*}', right: '\\end{align*}', display: true},
                    {left: '\\begin{alignat}', right: '\\end{alignat}', display: true},
                    {left: '\\begin{alignat*}', right: '\\end{alignat*}', display: true},
                    {left: '\\begin{gather}', right: '\\end{gather}', display: true},
                    {left: '\\begin{gather*}', right: '\\end{gather*}', display: true},
                    {left: '\\begin{multline}', right: '\\end{multline}', display: true},
                    {left: '\\begin{multline*}', right: '\\end{multline*}', display: true},
                ],
                throwOnError: false,
                errorColor: '#cc0000',
                strict: false,
                trust: false,
                macros: {
                    "\\RR": "\\mathbb{R}",
                    "\\QQ": "\\mathbb{Q}",
                    "\\ZZ": "\\mathbb{Z}",
                    "\\NN": "\\mathbb{N}",
                    "\\CC": "\\mathbb{C}",
                    "\\FF": "\\mathbb{F}",
                    "\\GL": "\\mathrm{GL}",
                    "\\SL": "\\mathrm{SL}",
                }
            });
        } catch (error) {
            console.error('LaTeX渲染错误:', error);
            previewDiv.innerHTML = '<span style="color: #e74c3c;">LaTeX渲染错误: ' + escapeHtml(error.message) + '</span>';
        }
    } else {
        // 如果KaTeX未加载，显示原始文本
        previewDiv.innerHTML = escapedText;
        // 显示提示信息
        if (previewDiv.querySelector('.katex-loading-message') === null) {
            const loadingMsg = document.createElement('div');
            loadingMsg.className = 'katex-loading-message';
            loadingMsg.style.cssText = 'color: #f39c12; font-size: 12px; margin-top: 10px;';
            loadingMsg.textContent = '正在加载LaTeX渲染引擎...';
            previewDiv.appendChild(loadingMsg);
        }
    }
}

// 辅助函数：通过label查找条目索引
function findItemIndexByLabel(label) {
    if (!label) return -1;
    return currentData.extracted_items.findIndex(item => item.label === label);
}

// 辅助函数：通过索引获取label（如果存在）
function getItemLabel(index) {
    if (index < 0 || index >= currentData.extracted_items.length) return null;
    return currentData.extracted_items[index].label;
}

// 更新依赖关系显示
function updateDependencies() {
    if (selectedItemIndex === null) return;
    
    const item = currentData.extracted_items[selectedItemIndex];
    dependenciesList.innerHTML = '';
    
    if (!item.dependencies || item.dependencies.length === 0) {
        dependenciesList.innerHTML = '<p style="color: #95a5a6; text-align: center; padding: 10px;">暂无依赖关系</p>';
        return;
    }
    
    item.dependencies.forEach(depIdentifier => {
        // 支持两种格式：label字符串或索引数字
        let depIndex = -1;
        let depLabel = null;
        
        if (typeof depIdentifier === 'string') {
            // 如果是label字符串
            depLabel = depIdentifier;
            depIndex = findItemIndexByLabel(depLabel);
        } else if (typeof depIdentifier === 'number') {
            // 如果是索引数字
            depIndex = depIdentifier;
            depLabel = getItemLabel(depIndex);
        }
        
        if (depIndex < 0 || depIndex >= currentData.extracted_items.length) {
            // 如果找不到对应的条目，显示为无效依赖
            const depCard = document.createElement('div');
            depCard.className = 'dependency-item';
            depCard.style.borderColor = '#e74c3c';
            
            const removeBtn = document.createElement('button');
            removeBtn.className = 'btn btn-danger';
            removeBtn.textContent = '删除';
            removeBtn.onclick = () => removeDependency(depIdentifier);
            
            depCard.innerHTML = `
                <div class="dependency-item-info">
                    <div class="dependency-item-label" style="color: #e74c3c;">
                        [无效] ${escapeHtml(depLabel || String(depIdentifier))}
                    </div>
                    <div class="dependency-item-preview" style="color: #95a5a6;">无法找到对应的条目</div>
                </div>
            `;
            depCard.appendChild(removeBtn);
            dependenciesList.appendChild(depCard);
            return;
        }
        
        const depItem = currentData.extracted_items[depIndex];
        const depCard = document.createElement('div');
        depCard.className = 'dependency-item';
        
        const preview = depItem.content ? 
            depItem.content.replace(/\\[a-zA-Z]+\{([^}]*)\}/g, '$1').substring(0, 80) : 
            '(无内容)';
        
        // 使用label作为标识符（如果存在），否则使用索引
        const identifier = depItem.label || depIndex;
        
        const removeBtn = document.createElement('button');
        removeBtn.className = 'btn btn-danger';
        removeBtn.textContent = '删除';
        removeBtn.onclick = () => removeDependency(identifier);
        
        depCard.innerHTML = `
            <div class="dependency-item-info">
                <div class="dependency-item-label">
                    [${depIndex}] ${depItem.type || 'unknown'}${depItem.label ? ': ' + escapeHtml(depItem.label) : ''}
                </div>
                <div class="dependency-item-preview">${escapeHtml(preview)}...</div>
            </div>
        `;
        depCard.appendChild(removeBtn);
        dependenciesList.appendChild(depCard);
    });
}

// 更新依赖选择下拉框
function updateDependencySelect() {
    if (selectedItemIndex === null) return;
    
    dependencySelect.innerHTML = '<option value="">选择要添加的依赖...</option>';
    
    const currentItem = currentData.extracted_items[selectedItemIndex];
    const existingDeps = currentItem.dependencies || [];
    
    currentData.extracted_items.forEach((item, index) => {
        if (index === selectedItemIndex) return; // 跳过自己
        
        // 检查是否已存在（支持label和索引两种格式）
        const itemLabel = item.label;
        const isAlreadyAdded = existingDeps.some(dep => {
            if (typeof dep === 'string') {
                return dep === itemLabel;
            } else if (typeof dep === 'number') {
                return dep === index;
            }
            return false;
        });
        
        if (isAlreadyAdded) {
            return; // 跳过已添加的依赖
        }
        
        const option = document.createElement('option');
        // 使用label作为值（如果存在），否则使用索引
        option.value = itemLabel || index;
        const label = itemLabel || `条目 ${index}`;
        const type = item.type || 'unknown';
        option.textContent = `[${index}] ${type}${itemLabel ? ': ' + itemLabel : ''}`;
        dependencySelect.appendChild(option);
    });
}

// 添加依赖
function addDependency() {
    if (selectedItemIndex === null) return;
    
    const selectedValue = dependencySelect.value;
    if (!selectedValue) return;
    
    const item = currentData.extracted_items[selectedItemIndex];
    if (!item.dependencies) {
        item.dependencies = [];
    }
    
    // 检查是否已存在（支持label和索引两种格式）
    const isAlreadyAdded = item.dependencies.some(dep => {
        if (typeof dep === 'string') {
            return dep === selectedValue;
        } else if (typeof dep === 'number') {
            // 如果selectedValue是label，需要查找对应的索引
            const depIndex = findItemIndexByLabel(selectedValue);
            return dep === depIndex || dep === parseInt(selectedValue);
        }
        return false;
    });
    
    if (!isAlreadyAdded) {
        // 优先使用label（如果存在），否则使用索引
        const depItem = currentData.extracted_items.find((it, idx) => {
            return it.label === selectedValue || idx === parseInt(selectedValue);
        });
        
        if (depItem && depItem.label) {
            // 使用label作为依赖标识符
            item.dependencies.push(depItem.label);
        } else {
            // 如果没有label，使用索引
            const depIndex = parseInt(selectedValue);
            if (!isNaN(depIndex)) {
                item.dependencies.push(depIndex);
            }
        }
        
        updateDependencies();
        updateDependencySelect();
        
        // 如果当前在图视图，更新图形
        if (currentView === 'graph' && network) {
            buildGraphData();
            renderGraph();
        }
    }
}

// 删除依赖（支持label字符串或索引数字）
function removeDependency(depIdentifier) {
    if (selectedItemIndex === null) return;
    
    const item = currentData.extracted_items[selectedItemIndex];
    if (item.dependencies) {
        // 将depIdentifier转换为正确的类型
        let targetIdentifier = depIdentifier;
        if (typeof depIdentifier === 'string') {
            // 如果是字符串，可能是label或数字字符串
            const numValue = parseInt(depIdentifier);
            if (!isNaN(numValue) && depIdentifier === numValue.toString()) {
                // 如果是纯数字字符串，转换为数字
                targetIdentifier = numValue;
            }
            // 否则保持为字符串（label）
        }
        
        item.dependencies = item.dependencies.filter(dep => {
            // 严格匹配：类型和值都要匹配
            if (typeof targetIdentifier === 'string' && typeof dep === 'string') {
                return dep !== targetIdentifier;
            } else if (typeof targetIdentifier === 'number' && typeof dep === 'number') {
                return dep !== targetIdentifier;
            }
            // 如果类型不匹配，尝试通过label查找索引
            if (typeof targetIdentifier === 'string' && typeof dep === 'number') {
                const depIndex = findItemIndexByLabel(targetIdentifier);
                return dep !== depIndex;
            }
            if (typeof targetIdentifier === 'number' && typeof dep === 'string') {
                const depLabel = getItemLabel(targetIdentifier);
                return dep !== depLabel;
            }
            return true;
        });
        updateDependencies();
        updateDependencySelect();
        
        // 如果当前在图视图，更新图形
        if (currentView === 'graph' && network) {
            buildGraphData();
            renderGraph();
        }
    }
}

// 保存当前条目
function saveCurrentItem() {
    if (selectedItemIndex === null) return;
    
    const item = currentData.extracted_items[selectedItemIndex];
    
    item.content = detailContent.value;
    item.proof = detailProof.value;
    item.comment = detailComment.value;
    
    // 显示保存成功提示
    const originalText = saveBtn.textContent;
    saveBtn.textContent = '已保存！';
    saveBtn.style.backgroundColor = '#27ae60';
    
    setTimeout(() => {
        saveBtn.textContent = originalText;
        saveBtn.style.backgroundColor = '';
    }, 2000);
    
    // 更新列表显示
    applyFilters();
    
    // 如果当前在图视图，更新图形
    if (currentView === 'graph' && network) {
        buildGraphData();
        renderGraph();
    }
}

// 导出JSON
function handleExport() {
    if (!currentData) return;
    
    const jsonString = JSON.stringify(currentData, null, 2);
    const blob = new Blob([jsonString], { type: 'application/json' });
    const url = URL.createObjectURL(blob);
    
    const a = document.createElement('a');
    a.href = url;
    a.download = currentFileName.replace('.json', '_edited.json') || 'exported_data.json';
    document.body.appendChild(a);
    a.click();
    document.body.removeChild(a);
    URL.revokeObjectURL(url);
}

// 工具函数：转义HTML
function escapeHtml(text) {
    const div = document.createElement('div');
    div.textContent = text;
    return div.innerHTML;
}

// 将removeDependency暴露到全局作用域，以便在动态生成的HTML中使用
window.removeDependency = removeDependency;

// ==================== 图视图相关函数 ====================

// 切换视图
function toggleView() {
    if (currentView === 'list') {
        currentView = 'graph';
        listView.style.display = 'none';
        graphView.style.display = 'flex';
        viewToggleBtn.textContent = '切换到列表视图';
        renderGraph();
    } else {
        currentView = 'list';
        listView.style.display = 'grid';
        graphView.style.display = 'none';
        viewToggleBtn.textContent = '切换到图视图';
    }
}

// 填充图视图的筛选器
function populateGraphFilters() {
    if (!currentData || !currentData.extracted_items) return;
    
    const types = new Set();
    currentData.extracted_items.forEach(item => {
        if (item.type) types.add(item.type);
    });
    
    // 填充类型筛选器（多选checkbox）
    const graphFilterTypeCheckboxes = document.getElementById('graph-filter-type-checkboxes');
    if (!graphFilterTypeCheckboxes) {
        console.warn('graph-filter-type-checkboxes 元素未找到');
        return;
    }
    
    graphFilterTypeCheckboxes.innerHTML = `
        <label class="checkbox-label">
            <input type="checkbox" class="graph-filter-type-checkbox" value="" checked>
            <span>全部</span>
        </label>
    `;
    Array.from(types).sort().forEach(type => {
        const label = document.createElement('label');
        label.className = 'checkbox-label';
        const checkbox = document.createElement('input');
        checkbox.type = 'checkbox';
        checkbox.className = 'graph-filter-type-checkbox';
        checkbox.value = type;
        checkbox.checked = true; // 默认全选
        const span = document.createElement('span');
        span.textContent = type;
        label.appendChild(checkbox);
        label.appendChild(span);
        graphFilterTypeCheckboxes.appendChild(label);
    });
}

// 处理图视图类型筛选变化
function handleGraphTypeFilterChange(event) {
    const checkboxes = document.querySelectorAll('.graph-filter-type-checkbox');
    const allCheckbox = Array.from(checkboxes).find(cb => cb.value === '');
    const target = event.target;
    
    // 如果点击了"全部"
    if (target.value === '') {
        if (target.checked) {
            // 选中全部时，选中所有其他checkbox
            checkboxes.forEach(cb => cb.checked = true);
        } else {
            // 取消"全部"时，不做任何操作（至少保留一个选中）
            target.checked = true;
        }
    } else {
        // 如果点击了其他类型
        const otherCheckboxes = Array.from(checkboxes).filter(cb => cb.value !== '');
        const allChecked = otherCheckboxes.every(cb => cb.checked);
        const noneChecked = otherCheckboxes.every(cb => !cb.checked);
        
        if (allChecked) {
            // 如果所有其他都选中，选中"全部"
            if (allCheckbox) allCheckbox.checked = true;
        } else if (noneChecked) {
            // 如果所有其他都取消，至少保留一个选中
            target.checked = true;
        } else {
            // 部分选中，取消"全部"
            if (allCheckbox) allCheckbox.checked = false;
        }
    }
    
    updateGraphFilter();
}

// 构建图数据
function buildGraphData() {
    if (!currentData || !currentData.extracted_items) return;
    
    const nodes = [];
    const edges = [];
    const nodeMap = new Map(); // label或index -> node id
    
    // 创建节点
    currentData.extracted_items.forEach((item, index) => {
        const nodeId = index;
        const label = item.label || `[${index}]`;
        const type = item.type || 'unknown';
        
        nodeMap.set(item.label || index, nodeId);
        
        // 根据类型设置颜色
        const colors = {
            'definition': { background: '#1976d2', border: '#1565c0' },
            'theorem': { background: '#7b1fa2', border: '#6a1b9a' },
            'lemma': { background: '#388e3c', border: '#2e7d32' },
            'proposition': { background: '#f57c00', border: '#e65100' },
            'corollary': { background: '#c2185b', border: '#ad1457' },
            'conjecture': { background: '#f9a825', border: '#f57f17' },
            'remark': { background: '#00796b', border: '#004d40' },
            'example': { background: '#689f38', border: '#558b2f' },
            'question': { background: '#512da8', border: '#4527a0' },
        };
        
        const color = colors[type] || { background: '#95a5a6', border: '#7f8c8d' };
        
        // 准备content预览（去除LaTeX命令，只保留文本）
        const contentPreview = item.content ? 
            item.content.replace(/\\[a-zA-Z]+\{([^}]*)\}/g, '$1')
                        .replace(/\$[^$]*\$/g, '')
                        .replace(/\\[a-zA-Z]+/g, '')
                        .substring(0, 200) : 
            '(无内容)';
        
        nodes.push({
            id: nodeId,
            label: label.length > 20 ? label.substring(0, 20) + '...' : label,
            title: `${type}: ${label}\n${item.section || ''}\n\n内容预览:\n${contentPreview}${item.content && item.content.length > 200 ? '...' : ''}`,
            color: color,
            font: { color: '#fff', size: 14 },
            shape: 'box',
            margin: 10,
            data: {
                index: index,
                type: type,
                label: item.label,
                section: item.section,
                content: item.content
            }
        });
    });
    
    // 创建边（依赖关系）
    currentData.extracted_items.forEach((item, fromIndex) => {
        if (!item.dependencies || item.dependencies.length === 0) return;
        
        item.dependencies.forEach(depIdentifier => {
            let toIndex = -1;
            
            if (typeof depIdentifier === 'string') {
                toIndex = findItemIndexByLabel(depIdentifier);
            } else if (typeof depIdentifier === 'number') {
                toIndex = depIdentifier;
            }
            
            if (toIndex >= 0 && toIndex < currentData.extracted_items.length && toIndex !== fromIndex) {
                edges.push({
                    from: fromIndex,
                    to: toIndex,
                    arrows: 'to',
                    color: { color: '#95a5a6', highlight: '#3498db' },
                    smooth: { type: 'curvedCW', roundness: 0.2 }
                });
            }
        });
    });
    
    graphData = { nodes: nodes, edges: edges };
}

// 渲染图形
function renderGraph() {
    // 检查vis.js是否已加载
    if (typeof vis === 'undefined' || !vis.Network) {
        console.error('vis.js未加载，无法渲染图形');
        graphContainer.innerHTML = '<div style="padding: 50px; text-align: center; color: #e74c3c;">vis.js库未加载，请检查网络连接</div>';
        return;
    }
    
    if (!graphData) {
        buildGraphData();
    }
    
    if (!graphData || !graphData.nodes || graphData.nodes.length === 0) {
        graphContainer.innerHTML = '<div style="padding: 50px; text-align: center; color: #95a5a6;">没有可显示的节点</div>';
        return;
    }
    
    // 应用筛选（多选类型）
    const selectedTypes = Array.from(document.querySelectorAll('.graph-filter-type-checkbox:checked'))
        .map(cb => cb.value)
        .filter(v => v !== ''); // 排除"全部"选项
    
    const allTypesSelected = document.querySelector('.graph-filter-type-checkbox[value=""]')?.checked || false;
    let filteredData = { ...graphData };
    
    if (!allTypesSelected && selectedTypes.length > 0) {
        const filteredNodes = graphData.nodes.filter(node => selectedTypes.includes(node.data.type));
        const filteredNodeIds = new Set(filteredNodes.map(n => n.id));
        const filteredEdges = graphData.edges.filter(edge => 
            filteredNodeIds.has(edge.from) && filteredNodeIds.has(edge.to)
        );
        filteredData = {
            nodes: new vis.DataSet(filteredNodes),
            edges: new vis.DataSet(filteredEdges)
        };
    } else {
        filteredData = {
            nodes: new vis.DataSet(graphData.nodes),
            edges: new vis.DataSet(graphData.edges)
        };
    }
    
    // 清理旧网络
    if (network) {
        network.destroy();
        network = null;
    }
    
    // 清空容器
    graphContainer.innerHTML = '';
    
    // 创建网络
    const options = getGraphOptions();
    network = new vis.Network(graphContainer, filteredData, options);
    
    // 添加事件监听
    network.on('click', function(params) {
        if (params.nodes.length > 0) {
            const nodeId = params.nodes[0];
            let nodeData;
            if (filteredData.nodes.get) {
                // 使用DataSet
                nodeData = filteredData.nodes.get(nodeId);
            } else {
                // 使用普通数组
                nodeData = filteredData.nodes.find(n => n.id === nodeId);
            }
            if (nodeData && nodeData.data) {
                // 显示content面板
                showGraphContent(nodeData.data);
            }
        } else {
            // 点击空白处关闭content面板
            graphContentPanel.style.display = 'none';
        }
    });
    
    network.on('doubleClick', function(params) {
        if (params.nodes.length > 0) {
            const nodeId = params.nodes[0];
            let nodeData;
            if (filteredData.nodes.get) {
                // 使用DataSet
                nodeData = filteredData.nodes.get(nodeId);
            } else {
                // 使用普通数组
                nodeData = filteredData.nodes.find(n => n.id === nodeId);
            }
            if (nodeData && nodeData.data) {
                // 切换到列表视图并选择该条目
                if (currentView === 'graph') {
                    toggleView();
                }
                selectItem(nodeData.data.index);
            }
        }
    });
}

// 获取图形选项
function getGraphOptions() {
    const layoutType = graphLayoutSelect.value;
    
    const baseOptions = {
        nodes: {
            shape: 'box',
            font: {
                size: 14,
                color: '#fff'
            },
            borderWidth: 2,
            shadow: true
        },
        edges: {
            arrows: {
                to: {
                    enabled: true,
                    scaleFactor: 1.2
                }
            },
            smooth: {
                type: 'curvedCW',
                roundness: 0.2
            },
            color: {
                color: '#95a5a6',
                highlight: '#3498db'
            }
        },
        physics: {
            enabled: true,
            stabilization: {
                iterations: 200
            }
        },
        interaction: {
            dragNodes: true,
            dragView: true,
            zoomView: true,
            hover: true,
            tooltipDelay: 100
        }
    };
    
    if (layoutType === 'hierarchical') {
        baseOptions.layout = {
            hierarchical: {
                direction: 'UD',
                sortMethod: 'directed',
                nodeSpacing: 150,
                levelSeparation: 200
            }
        };
        baseOptions.physics.enabled = false;
    } else if (layoutType === 'force') {
        baseOptions.physics = {
            enabled: true,
            forceAtlas2Based: {
                gravitationalConstant: -50,
                centralGravity: 0.01,
                springLength: 200,
                springConstant: 0.08
            },
            maxVelocity: 50,
            solver: 'forceAtlas2Based',
            timestep: 0.35,
            stabilization: {
                enabled: true,
                iterations: 200,
                updateInterval: 25
            }
        };
    } else if (layoutType === 'circular') {
        baseOptions.layout = {
            improvedLayout: true,
            randomSeed: 2
        };
        baseOptions.physics = {
            enabled: true,
            barnesHut: {
                gravitationalConstant: -2000,
                centralGravity: 0.3,
                springLength: 200,
                springConstant: 0.04,
                damping: 0.09,
                avoidOverlap: 0.1
            },
            stabilization: {
                enabled: true,
                iterations: 1000,
                updateInterval: 25
            }
        };
    }
    
    return baseOptions;
}

// 更新图形布局
function updateGraphLayout() {
    if (network && graphData) {
        renderGraph();
    }
}

// 更新图形筛选
function updateGraphFilter() {
    if (network && graphData) {
        renderGraph();
    }
}

// 重置图形视图
function resetGraphView() {
    if (network) {
        network.setOptions(getGraphOptions());
        network.fit();
    }
}

// 适应窗口
function fitGraphView() {
    if (network) {
        network.fit({
            animation: {
                duration: 500,
                easingFunction: 'easeInOutQuad'
            }
        });
    }
}

// 显示图节点的content
function showGraphContent(nodeData) {
    if (!nodeData) return;
    
    const item = currentData.extracted_items[nodeData.index];
    if (!item) return;
    
    graphContentTitle.textContent = `${item.type || 'unknown'}${item.label ? ': ' + item.label : ' [条目 ' + nodeData.index + ']'}`;
    
    let contentHtml = '';
    
    if (item.section) {
        contentHtml += `<p><strong>章节:</strong> ${escapeHtml(item.section)}</p>`;
    }
    
    if (item.content) {
        contentHtml += `<div><strong>内容:</strong></div>`;
        contentHtml += `<div class="latex-preview" id="graph-content-latex">${escapeHtml(item.content)}</div>`;
    } else {
        contentHtml += `<p style="color: #95a5a6;">(无内容)</p>`;
    }
    
    graphContentBody.innerHTML = contentHtml;
    graphContentPanel.style.display = 'flex';
    
    // 渲染LaTeX
    if (item.content && typeof renderMathInElement !== 'undefined') {
        setTimeout(() => {
            const latexDiv = document.getElementById('graph-content-latex');
            if (latexDiv) {
                try {
                    renderMathInElement(latexDiv, {
                        delimiters: [
                            {left: '$$', right: '$$', display: true},
                            {left: '$', right: '$', display: false},
                            {left: '\\[', right: '\\]', display: true},
                            {left: '\\(', right: '\\)', display: false},
                            {left: '\\begin{equation}', right: '\\end{equation}', display: true},
                            {left: '\\begin{equation*}', right: '\\end{equation*}', display: true},
                            {left: '\\begin{align}', right: '\\end{align}', display: true},
                            {left: '\\begin{align*}', right: '\\end{align*}', display: true},
                        ],
                        throwOnError: false,
                        errorColor: '#cc0000',
                        strict: false,
                        trust: false
                    });
                } catch (error) {
                    console.error('LaTeX渲染错误:', error);
                }
            }
        }, 100);
    }
}
