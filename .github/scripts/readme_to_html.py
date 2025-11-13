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

    # Convert headers
    html = re.sub(r'^# (.*?)$', r'<h1>\1</h1>', html, flags=re.MULTILINE)
    html = re.sub(r'^## (.*?)$', r'<h2>\1</h2>', html, flags=re.MULTILINE)
    html = re.sub(r'^### (.*?)$', r'<h3>\1</h3>', html, flags=re.MULTILINE)
    html = re.sub(r'^#### (.*?)$', r'<h4>\1</h4>', html, flags=re.MULTILINE)

    # Convert bold and italic
    html = re.sub(r'\*\*(.*?)\*\*', r'<strong>\1</strong>', html)
    html = re.sub(r'\*(.*?)\*', r'<em>\1</em>', html)
    html = re.sub(r'`([^`]+)`', r'<code>\1</code>', html)

    # Convert links
    html = re.sub(r'\[([^\]]+)\]\(([^\)]+)\)', r'<a href="\2">\1</a>', html)

    # Convert images
    html = re.sub(r'!\[([^\]]*)\]\(([^\)]+)\)', r'<img src="\2" alt="\1" />', html)

    # Convert code blocks
    html = re.sub(r'```lean\n(.*?)\n```', r'<pre><code class="language-lean">\1</code></pre>', html, flags=re.DOTALL)
    html = re.sub(r'```bash\n(.*?)\n```', r'<pre><code class="language-bash">\1</code></pre>', html, flags=re.DOTALL)
    html = re.sub(r'```(.*?)\n(.*?)\n```', r'<pre><code>\2</code></pre>', html, flags=re.DOTALL)

    # Convert unordered lists
    html = re.sub(r'^\- (.*?)$', r'<li>\1</li>', html, flags=re.MULTILINE)
    html = re.sub(r'((?:<li>.*?</li>\n?)+)', r'<ul>\1</ul>', html, flags=re.DOTALL)

    # Convert paragraphs (lines separated by blank lines)
    paragraphs = []
    current_p = []
    for line in html.split('\n'):
        line = line.strip()
        if line and not line.startswith('<'):
            current_p.append(line)
        else:
            if current_p:
                paragraphs.append('<p>' + ' '.join(current_p) + '</p>')
                current_p = []
            if line:
                paragraphs.append(line)
    if current_p:
        paragraphs.append('<p>' + ' '.join(current_p) + '</p>')

    html = '\n'.join(paragraphs)

    # Handle badges (convert to simple links)
    html = re.sub(r'<p>\[<img[^>]*alt="([^"]*)"[^>]*>\]\(([^\)]+)\)</p>', r'<div class="badge"><a href="\2">\1</a></div>', html)

    # Handle details/summary
    html = re.sub(r'<details>(.*?)</details>', r'<details class="collapsible">\1</details>', html, flags=re.DOTALL)
    html = re.sub(r'<summary>(.*?)</summary>', r'<summary>\1</summary>', html)

    return html


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

        .badge a {{
            background: #3498db;
            color: white;
            padding: 0.25rem 0.75rem;
            border-radius: 3px;
            font-size: 0.85rem;
            text-decoration: none;
        }}

        .badge a:hover {{
            background: #2980b9;
            text-decoration: none;
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
