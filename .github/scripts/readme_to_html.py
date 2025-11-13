#!/usr/bin/env python3
"""
Convert README.md to HTML with clean academic styling matching blueprint aesthetic.
"""

import re
import sys
from pathlib import Path


def markdown_to_html(md_content):
    """Convert markdown to HTML with basic formatting."""
    html = md_content

    # Step 1: Protect and convert code blocks FIRST (before any other processing)
    code_blocks = []
    def save_code_block(match):
        code_blocks.append(match.group(0))
        return f'__CODE_BLOCK_{len(code_blocks)-1}__'

    # Fenced code blocks with language
    html = re.sub(r'```(\w+)\n(.*?)\n```',
                  lambda m: save_code_block(m) or f'<pre><code class="language-{m.group(1)}">{escape_html(m.group(2))}</code></pre>',
                  html, flags=re.DOTALL)
    # Fenced code blocks without language
    html = re.sub(r'```\n(.*?)\n```',
                  lambda m: save_code_block(m) or f'<pre><code>{escape_html(m.group(1))}</code></pre>',
                  html, flags=re.DOTALL)

    # Step 2: Convert headers (before links so [text](#anchor) in headers works)
    html = re.sub(r'^#### (.*?)$', r'<h4>\1</h4>', html, flags=re.MULTILINE)
    html = re.sub(r'^### (.*?)$', r'<h3>\1</h3>', html, flags=re.MULTILINE)
    html = re.sub(r'^## (.*?)$', r'<h2>\1</h2>', html, flags=re.MULTILINE)
    html = re.sub(r'^# (.*?)$', r'<h1>\1</h1>', html, flags=re.MULTILINE)

    # Step 3: Convert tables (before images/links to avoid interference)
    html = convert_tables(html)

    # Step 4: Convert badges (special case: [![alt](image)](link) pattern)
    # This must happen before general image/link conversion
    html = re.sub(r'\[\!\[([^\]]*)\]\(([^\)]+)\)\]\(([^\)]+)\)',
                  r'<div class="badge"><a href="\3"><img src="\2" alt="\1" /></a></div>',
                  html)

    # Step 5: Convert images (BEFORE links, since images start with !)
    html = re.sub(r'!\[([^\]]*)\]\(([^\)]+)\)', r'<img src="\2" alt="\1" />', html)

    # Step 6: Convert links
    html = re.sub(r'\[([^\]]+)\]\(([^\)]+)\)', r'<a href="\2">\1</a>', html)

    # Step 7: Convert bold and italic (after links to avoid interference)
    html = re.sub(r'\*\*([^\*]+)\*\*', r'<strong>\1</strong>', html)
    html = re.sub(r'\*([^\*]+)\*', r'<em>\1</em>', html)

    # Step 8: Convert inline code (after bold/italic to avoid conflicts)
    html = re.sub(r'`([^`]+)`', r'<code>\1</code>', html)

    # Step 9: Convert lists
    html = convert_lists(html)

    # Step 10: Handle details/summary (HTML pass-through)
    html = re.sub(r'<details>', r'<details class="collapsible">', html)

    # Step 11: Convert remaining text to paragraphs (LAST step)
    html = wrap_paragraphs(html)

    return html


def escape_html(text):
    """Escape HTML special characters."""
    return (text.replace('&', '&amp;')
                .replace('<', '&lt;')
                .replace('>', '&gt;')
                .replace('"', '&quot;')
                .replace("'", '&#39;'))


def convert_tables(html):
    """Convert markdown tables to HTML tables."""
    lines = html.split('\n')
    result = []
    in_table = False
    table_lines = []

    for line in lines:
        # Detect table rows (lines with | separators)
        if '|' in line and line.strip().startswith('|'):
            if not in_table:
                in_table = True
                table_lines = []
            table_lines.append(line)
        else:
            # End of table
            if in_table:
                result.append(render_table(table_lines))
                in_table = False
                table_lines = []
            result.append(line)

    # Handle table at end of file
    if in_table:
        result.append(render_table(table_lines))

    return '\n'.join(result)


def render_table(table_lines):
    """Render markdown table as HTML."""
    if len(table_lines) < 2:
        return '\n'.join(table_lines)  # Not a valid table

    html = ['<table>']

    for i, line in enumerate(table_lines):
        # Skip separator line (contains only |, -, and spaces)
        if re.match(r'^\s*\|[\s\-:|]+\|\s*$', line):
            continue

        # Parse cells
        cells = [cell.strip() for cell in line.strip('|').split('|')]

        # First row is header
        if i == 0:
            html.append('<thead><tr>')
            for cell in cells:
                html.append(f'<th>{cell}</th>')
            html.append('</tr></thead><tbody>')
        else:
            html.append('<tr>')
            for cell in cells:
                html.append(f'<td>{cell}</td>')
            html.append('</tr>')

    html.append('</tbody></table>')
    return '\n'.join(html)


def convert_lists(html):
    """Convert markdown lists to HTML lists."""
    lines = html.split('\n')
    result = []
    in_list = False
    list_items = []

    for line in lines:
        # Unordered list item
        if re.match(r'^\s*[-*+]\s+', line):
            item = re.sub(r'^\s*[-*+]\s+', '', line)
            if not in_list:
                in_list = True
                list_items = []
            list_items.append(f'<li>{item}</li>')
        else:
            # End of list
            if in_list:
                result.append('<ul>')
                result.extend(list_items)
                result.append('</ul>')
                in_list = False
                list_items = []
            result.append(line)

    # Handle list at end of file
    if in_list:
        result.append('<ul>')
        result.extend(list_items)
        result.append('</ul>')

    return '\n'.join(result)


def wrap_paragraphs(html):
    """Wrap text that isn't already in HTML tags into paragraphs."""
    lines = html.split('\n')
    result = []
    paragraph_lines = []

    for line in lines:
        line = line.strip()

        # Skip empty lines
        if not line:
            if paragraph_lines:
                result.append('<p>' + ' '.join(paragraph_lines) + '</p>')
                paragraph_lines = []
            result.append('')
            continue

        # If line starts with HTML tag, it's already formatted
        if line.startswith('<'):
            if paragraph_lines:
                result.append('<p>' + ' '.join(paragraph_lines) + '</p>')
                paragraph_lines = []
            result.append(line)
        else:
            # Accumulate plain text lines
            paragraph_lines.append(line)

    # Handle paragraph at end
    if paragraph_lines:
        result.append('<p>' + ' '.join(paragraph_lines) + '</p>')

    return '\n'.join(result)


def create_html_page(md_content):
    """Create full HTML page with styling."""
    content_html = markdown_to_html(md_content)

    return f'''<!DOCTYPE html>
<html lang="en">
<head>
    <meta charset="UTF-8">
    <meta name="viewport" content="width=device-width, initial-scale=1.0">
    <title>Chebyshev Circles - Formal Verification</title>
    <style>
        * {{
            margin: 0;
            padding: 0;
            box-sizing: border-box;
        }}

        body {{
            font-family: -apple-system, BlinkMacSystemFont, 'Segoe UI', Roboto, 'Helvetica Neue', Arial, sans-serif;
            line-height: 1.6;
            color: #333;
            background: #f5f5f5;
        }}

        .header {{
            background: #fff;
            border-bottom: 1px solid #e0e0e0;
            padding: 1rem 0;
            position: sticky;
            top: 0;
            z-index: 100;
            box-shadow: 0 2px 4px rgba(0,0,0,0.05);
        }}

        .header-content {{
            max-width: 1200px;
            margin: 0 auto;
            padding: 0 2rem;
            display: flex;
            justify-content: space-between;
            align-items: center;
        }}

        .header h1 {{
            font-size: 1.5rem;
            color: #2c3e50;
        }}

        .nav {{
            display: flex;
            gap: 1.5rem;
        }}

        .nav a {{
            color: #2c3e50;
            text-decoration: none;
            font-weight: 500;
            padding: 0.5rem 1rem;
            border-radius: 4px;
            transition: background 0.2s;
        }}

        .nav a:hover {{
            background: #f0f0f0;
        }}

        .container {{
            max-width: 1200px;
            margin: 2rem auto;
            padding: 0 2rem;
            background: #fff;
            border-radius: 8px;
            box-shadow: 0 1px 3px rgba(0,0,0,0.1);
        }}

        .content {{
            padding: 3rem;
        }}

        h1 {{
            font-size: 2.5rem;
            margin-bottom: 1.5rem;
            color: #2c3e50;
            border-bottom: 2px solid #e0e0e0;
            padding-bottom: 0.5rem;
        }}

        h2 {{
            font-size: 2rem;
            margin-top: 2.5rem;
            margin-bottom: 1rem;
            color: #34495e;
        }}

        h3 {{
            font-size: 1.5rem;
            margin-top: 2rem;
            margin-bottom: 0.75rem;
            color: #34495e;
        }}

        h4 {{
            font-size: 1.25rem;
            margin-top: 1.5rem;
            margin-bottom: 0.5rem;
            color: #34495e;
        }}

        p {{
            margin-bottom: 1rem;
        }}

        a {{
            color: #3498db;
            text-decoration: none;
        }}

        a:hover {{
            text-decoration: underline;
        }}

        code {{
            background: #f8f9fa;
            padding: 0.2em 0.4em;
            border-radius: 3px;
            font-family: 'Courier New', monospace;
            font-size: 0.9em;
            color: #e74c3c;
        }}

        pre {{
            background: #f8f9fa;
            border-left: 4px solid #3498db;
            padding: 1rem;
            margin: 1.5rem 0;
            overflow-x: auto;
            border-radius: 4px;
        }}

        pre code {{
            background: none;
            padding: 0;
            color: #333;
            font-size: 0.9rem;
        }}

        img {{
            max-width: 100%;
            height: auto;
            display: block;
            margin: 2rem auto;
            border-radius: 4px;
            box-shadow: 0 2px 8px rgba(0,0,0,0.1);
        }}

        ul, ol {{
            margin-left: 2rem;
            margin-bottom: 1rem;
        }}

        li {{
            margin-bottom: 0.5rem;
        }}

        table {{
            width: 100%;
            border-collapse: collapse;
            margin: 1.5rem 0;
        }}

        th, td {{
            padding: 0.75rem;
            text-align: left;
            border: 1px solid #e0e0e0;
        }}

        th {{
            background: #f8f9fa;
            font-weight: 600;
        }}

        .badge {{
            display: inline-block;
            margin-right: 0.5rem;
            margin-bottom: 0.5rem;
        }}

        .badge img {{
            display: inline-block;
            margin: 0;
            box-shadow: none;
            vertical-align: middle;
        }}

        details {{
            margin: 1rem 0;
            border: 1px solid #e0e0e0;
            border-radius: 4px;
            padding: 1rem;
        }}

        summary {{
            font-weight: 600;
            cursor: pointer;
            user-select: none;
        }}

        summary:hover {{
            color: #3498db;
        }}
    </style>
</head>
<body>
    <div class="header">
        <div class="header-content">
            <h1>Chebyshev Circles</h1>
            <nav class="nav">
                <a href="./blueprint/">Blueprint</a>
                <a href="./docs/">API Docs</a>
                <a href="./graph/">Dependency Graph</a>
                <a href="https://github.com/e-vergo/ChebyshevCircles">GitHub</a>
            </nav>
        </div>
    </div>

    <div class="container">
        <div class="content">
            {content_html}
        </div>
    </div>
</body>
</html>'''


def main():
    if len(sys.argv) < 3:
        print("Usage: readme_to_html.py <input_md> <output_html>")
        sys.exit(1)

    input_file = Path(sys.argv[1])
    output_file = Path(sys.argv[2])

    if not input_file.exists():
        print(f"Error: Input file '{input_file}' not found")
        sys.exit(1)

    md_content = input_file.read_text(encoding='utf-8')
    html_content = create_html_page(md_content)

    output_file.write_text(html_content, encoding='utf-8')
    print(f"Successfully converted {input_file} to {output_file}")


if __name__ == '__main__':
    main()
