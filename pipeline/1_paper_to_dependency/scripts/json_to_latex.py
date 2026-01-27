#!/usr/bin/env python3
"""
将JSON格式的数学内容转换为Lean Blueprint风格的LaTeX格式
"""

import json
import sys
import os
from typing import Dict, List, Optional


def get_latex_environment(item_type: str) -> str:
    """根据item类型返回对应的LaTeX环境名"""
    type_mapping = {
        "theorem": "theorem",
        "definition": "definition",
        "remark": "remark",
        "conjecture": "conjecture",
        "lemma": "lemma",
        "proposition": "proposition",
        "example": "example",
        "notation": "notation",
        "question": "remark",  # 问题用remark环境
        "corollary": "corollary",
    }
    return type_mapping.get(item_type.lower(), "theorem")


def label_to_lean_name(label: Optional[str]) -> str:
    """从label生成lean名称（去掉前缀，转换为snake_case）"""
    if not label:
        return ""
    
    # 去掉常见前缀（如L:, D:, T:等）
    parts = label.split(":", 1)
    if len(parts) > 1:
        name = parts[1]
    else:
        name = parts[0]
    
    # 转换为snake_case（简单处理：空格和特殊字符替换为下划线）
    name = name.replace(" ", "_").replace("-", "_")
    # 移除特殊字符，只保留字母数字和下划线
    name = "".join(c if c.isalnum() or c == "_" else "_" for c in name)
    # 移除连续的下划线
    while "__" in name:
        name = name.replace("__", "_")
    # 转换为小写
    name = name.lower()
    
    return name


def format_dependencies(dependencies: List[str]) -> str:
    """格式化依赖列表为\\uses命令"""
    if not dependencies:
        return ""
    return "\\uses{" + ", ".join(dependencies) + "}"


def convert_item_to_latex(item: Dict) -> str:
    """将单个item转换为LaTeX格式"""
    item_type = item.get("type", "theorem")
    label = item.get("label")
    content = item.get("content", "")
    proof = item.get("proof")
    dependencies = item.get("dependencies", [])
    
    # 获取LaTeX环境名
    env_name = get_latex_environment(item_type)
    
    # 构建LaTeX代码
    lines = []
    
    # 开始环境（不包含可选参数，label单独一行）
    lines.append(f"\\begin{{{env_name}}}")
    
    # 添加label（如果存在）
    if label:
        # 检查content开头是否有单独的\label命令（不是equation等环境中的）
        content_stripped = content.strip()
        has_standalone_label = False
        if content_stripped.startswith(f"\\label{{{label}}}"):
            # 检查是否是单独的一行
            first_line = content.split("\n")[0].strip()
            if first_line == f"\\label{{{label}}}":
                has_standalone_label = True
        
        # 如果没有独立的label行，添加label
        if not has_standalone_label:
            lines.append(f"    \\label{{{label}}}")
    
    # 添加lean相关命令
    lean_name = label_to_lean_name(label)
    if lean_name:
        lines.append(f"    \\lean{{{lean_name}}}")
    lines.append("    \\leanok")
    
    # 添加依赖
    if dependencies:
        uses_cmd = format_dependencies(dependencies)
        lines.append(f"    {uses_cmd}")
    
    # 添加内容
    content_lines = content.split("\n")
    # 处理第一行：如果包含与item label相同的\label命令，移除它
    if label and content_lines:
        first_line = content_lines[0]
        # 检查是否包含\label{label}
        label_pattern = f"\\label{{{label}}}"
        if label_pattern in first_line:
            # 移除label部分
            first_line = first_line.replace(label_pattern, "").strip()
            # 如果移除label后还有内容，保留；如果为空，跳过这一行
            if first_line:
                content_lines[0] = first_line
            else:
                content_lines = content_lines[1:]
    
    for line in content_lines:
        # 添加内容，保持原有缩进
        if line.strip():
            # 如果内容行没有缩进，添加适当的缩进
            if not line.startswith(" "):
                lines.append("    " + line)
            else:
                lines.append(line)
        else:
            lines.append("")
    
    # 结束环境
    lines.append(f"\\end{{{env_name}}}")
    
    # 如果有证明，添加proof环境
    if proof:
        lines.append("")
        lines.append("\\begin{proof}")
        lines.append("    \\leanok")
        if dependencies:
            uses_cmd = format_dependencies(dependencies)
            lines.append(f"    {uses_cmd}")
        
        # 添加证明内容
        proof_lines = proof.split("\n")
        for line in proof_lines:
            if line.strip():
                if not line.startswith(" "):
                    lines.append("    " + line)
                else:
                    lines.append(line)
            else:
                lines.append("")
        
        lines.append("\\end{proof}")
    
    return "\n".join(lines)


def convert_json_to_latex(json_file: str, output_file: Optional[str] = None) -> str:
    """将JSON文件转换为LaTeX格式"""
    # 读取JSON文件
    with open(json_file, 'r', encoding='utf-8') as f:
        data = json.load(f)
    
    # 获取所有items
    items = data.get("extracted_items", [])
    
    # 转换为LaTeX
    latex_parts = []
    for item in items:
        latex_item = convert_item_to_latex(item)
        latex_parts.append(latex_item)
        latex_parts.append("")  # 添加空行分隔
    
    # 合并所有LaTeX内容
    latex_content = "\n".join(latex_parts)
    
    # 写入输出文件
    if output_file:
        with open(output_file, 'w', encoding='utf-8') as f:
            f.write(latex_content)
        print(f"已成功转换并保存到: {output_file}")
    else:
        # 如果没有指定输出文件，生成默认文件名
        base_name = os.path.splitext(os.path.basename(json_file))[0]
        output_file = f"{base_name}_blueprint.tex"
        with open(output_file, 'w', encoding='utf-8') as f:
            f.write(latex_content)
        print(f"已成功转换并保存到: {output_file}")
    
    return latex_content


def main():
    """主函数"""
    if len(sys.argv) < 2:
        print("用法: python json_to_latex.py <input_json_file> [output_tex_file]")
        sys.exit(1)
    
    input_file = sys.argv[1]
    output_file = sys.argv[2] if len(sys.argv) > 2 else None
    
    if not os.path.exists(input_file):
        print(f"错误: 文件 '{input_file}' 不存在")
        sys.exit(1)
    
    try:
        convert_json_to_latex(input_file, output_file)
    except Exception as e:
        print(f"错误: {e}")
        sys.exit(1)


if __name__ == "__main__":
    main()
