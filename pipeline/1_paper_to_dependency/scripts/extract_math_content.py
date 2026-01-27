#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
从LaTeX数学论文中提取记号、定义、定理、引理等内容
"""

import re
import json
import os
from pathlib import Path
from typing import List, Dict, Optional, Tuple


class LaTeXExtractor:
    """LaTeX内容提取器"""
    
    # 需要提取的环境类型
    EXTRACT_ENVIRONMENTS = {
        'notation', 'definition', 'theorem', 'lemma', 'proposition',
        'corollary', 'conjecture', 'remark', 'example', 'question',
        'statement', 'hypothesis', 'construction', 'caution', 'convention',
        'keylemma', 'lemmanotation', 'definition-lemma', 'definition-proposition',
        'graphs', 'caveat'
    }
    
    # 需要提取证明的环境类型
    PROOF_ENVIRONMENTS = {'theorem', 'lemma', 'proposition', 'corollary', 
                         'keylemma', 'lemmanotation', 'definition-lemma', 
                         'definition-proposition'}
    
    def __init__(self):
        self.extracted_items = []
        
    def extract_from_file(self, file_path: str) -> Dict:
        """从单个.tex文件提取内容"""
        print(f"正在处理文件: {file_path}")
        
        with open(file_path, 'r', encoding='utf-8') as f:
            content = f.read()
        
        # 重置状态
        self.extracted_items = []
        
        # 提取所有内容
        self._extract_environments(content)
        
        return {
            'file_name': os.path.basename(file_path),
            'extracted_items': self.extracted_items
        }
    
    def _get_section_at_line(self, lines: List[str], line_num: int) -> Tuple[Optional[str], Optional[str]]:
        """获取指定行号处的section和subsection"""
        section = None
        subsection = None
        
        # 从文件开头到指定行查找最近的section/subsection
        for i in range(line_num + 1):
            line = lines[i]
            
            # 匹配section
            section_match = re.search(r'\\section\{([^}]+)\}', line)
            if section_match:
                section = section_match.group(1)
                subsection = None  # section改变时重置subsection
            
            # 匹配subsection
            subsection_match = re.search(r'\\subsection\{([^}]+)\}', line)
            if subsection_match:
                subsection = subsection_match.group(1)
        
        return section, subsection
    
    def _extract_environments(self, content: str):
        """提取所有环境内容"""
        lines = content.split('\n')
        i = 0
        
        while i < len(lines):
            line = lines[i]
            
            # 检查环境开始
            env_match = re.search(r'\\begin\{([^}]+)\}', line)
            if env_match:
                env_name = env_match.group(1)
                
                if env_name in self.EXTRACT_ENVIRONMENTS:
                    # 获取当前行号对应的section/subsection
                    section, subsection = self._get_section_at_line(lines, i)
                    
                    # 提取环境内容
                    env_content, end_line, label = self._extract_environment(
                        lines, i, env_name
                    )
                    
                    if env_content:
                        item = {
                            'type': env_name,
                            'label': label,
                            'content': env_content,
                            'section': section,
                            'subsection': subsection,
                            'line_number': i + 1,
                            'proof': None
                        }
                        
                        # 如果是theorem/lemma等，查找紧接其后的proof
                        if env_name in self.PROOF_ENVIRONMENTS:
                            proof_content, proof_end = self._find_next_proof(lines, end_line)
                            if proof_content:
                                item['proof'] = proof_content
                        
                        # 提取依赖（从content和proof中提取\ref{...}）
                        item['dependencies'] = self._extract_dependencies(item.get('content', ''), item.get('proof'))
                        
                        self.extracted_items.append(item)
                    
                    i = end_line
                else:
                    i += 1
            else:
                i += 1
    
    def _extract_environment(self, lines: List[str], start_line: int, env_name: str) -> Tuple[str, int, Optional[str]]:
        """提取环境内容，返回(内容, 结束行号, label)
        使用计数器处理嵌套的同名环境
        """
        content_lines = []
        label = None
        env_depth = 0  # 环境嵌套深度
        i = start_line
        
        # 查找label（可能在\begin{env}同一行或下一行）
        label_pattern = re.compile(r'\\label\{([^}]+)\}')
        begin_pattern = re.compile(rf'\\begin\{{{re.escape(env_name)}\}}')
        end_pattern = re.compile(rf'\\end\{{{re.escape(env_name)}\}}')
        
        while i < len(lines):
            line = lines[i]
            
            # 检查环境开始
            if begin_pattern.search(line):
                if env_depth == 0:
                    # 第一次遇到开始，检查label
                    label_match = label_pattern.search(line)
                    if label_match:
                        label = label_match.group(1)
                env_depth += 1
                
                # 如果是第一次开始，跳过这一行（不包含在内容中）
                if env_depth == 1:
                    i += 1
                    continue
            
            # 检查环境结束
            if end_pattern.search(line):
                env_depth -= 1
                if env_depth == 0:
                    # 环境完全结束
                    break
            
            # 如果环境已开始，添加到内容
            if env_depth > 0:
                # 检查label（可能在后续行）
                if label is None:
                    label_match = label_pattern.search(line)
                    if label_match:
                        label = label_match.group(1)
                
                content_lines.append(line)
            
            i += 1
        
        content = '\n'.join(content_lines).strip()
        return content, i, label
    
    def _extract_dependencies(self, content: str, proof: Optional[str] = None) -> List[str]:
        """从content和proof中提取所有\ref{...}依赖
        
        Args:
            content: 内容文本
            proof: 证明文本（可选）
            
        Returns:
            依赖label列表（去重后）
        """
        dependencies = set()
        
        # 匹配\ref{label}模式
        # 支持多种格式：
        # - \ref{label}
        # - ~\ref{label}
        # - Theorem~\ref{label}
        # - \eqref{label}
        ref_pattern = re.compile(r'\\(?:eq)?ref\{([^}]+)\}')
        
        # 从content中提取
        if content:
            matches = ref_pattern.findall(content)
            dependencies.update(matches)
        
        # 从proof中提取
        if proof:
            matches = ref_pattern.findall(proof)
            dependencies.update(matches)
        
        # 返回排序后的列表（去重）
        return sorted(list(dependencies))
    
    def _find_next_proof(self, lines: List[str], start_line: int) -> Tuple[Optional[str], int]:
        """查找紧接在start_line之后的proof环境"""
        i = start_line + 1
        proof_started = False
        proof_lines = []
        
        # 跳过空行和注释
        while i < len(lines):
            line = lines[i].strip()
            
            # 跳过空行
            if not line:
                i += 1
                continue
            
            # 跳过注释
            if line.startswith('%'):
                i += 1
                continue
            
            # 检查是否有其他环境开始（非proof）
            other_env_match = re.search(r'\\begin\{([^}]+)\}', line)
            if other_env_match and other_env_match.group(1) != 'proof':
                # 如果遇到非proof环境，说明没有紧接的proof
                break
            
            # 检查proof开始
            if re.search(r'\\begin\{proof\}', line):
                proof_started = True
                # 提取proof内容
                proof_content, end_line, _ = self._extract_environment(lines, i, 'proof')
                if proof_content:
                    return proof_content, end_line
                break
            
            # 如果已经过了几行还没找到proof，可能没有紧接的proof
            if i > start_line + 10:  # 最多查找10行
                break
            
            i += 1
        
        return None, i
    
    def save_to_json(self, data: Dict, output_path: str):
        """保存提取的数据到JSON文件"""
        with open(output_path, 'w', encoding='utf-8') as f:
            json.dump(data, f, ensure_ascii=False, indent=2)
        print(f"已保存到: {output_path}")


def main():
    """主函数"""
    # 设置路径
    data_dir = Path(__file__).parent / 'data'
    output_dir = Path(__file__).parent / 'output'
    output_dir.mkdir(exist_ok=True)
    
    # 创建提取器
    extractor = LaTeXExtractor()
    
    # 处理所有.tex文件
    tex_files = list(data_dir.glob('*.tex'))
    
    if not tex_files:
        print(f"在 {data_dir} 中未找到.tex文件")
        return
    
    for tex_file in tex_files:
        try:
            # 提取内容
            data = extractor.extract_from_file(str(tex_file))
            
            # 保存JSON
            output_file = output_dir / f"{tex_file.stem}.json"
            extractor.save_to_json(data, str(output_file))
            
            print(f"提取完成: {len(data['extracted_items'])} 个项目\n")
            
        except Exception as e:
            print(f"处理 {tex_file} 时出错: {e}")
            import traceback
            traceback.print_exc()


if __name__ == '__main__':
    main()
