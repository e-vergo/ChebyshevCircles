#!/bin/bash
# Create dependency graph visualization page

set -e

OUTPUT_DIR="$1"
PDF_FILE="$2"

if [ -z "$OUTPUT_DIR" ] || [ -z "$PDF_FILE" ]; then
    echo "Usage: create_graph_page.sh <output_dir> <pdf_file>"
    exit 1
fi

mkdir -p "$OUTPUT_DIR"

cat > "$OUTPUT_DIR/index.html" << 'EOF'
<!DOCTYPE html>
<html lang="en">
<head>
    <meta charset="UTF-8">
    <meta name="viewport" content="width=device-width, initial-scale=1.0">
    <title>Dependency Graph - Chebyshev Circles</title>
    <style>
        * {
            margin: 0;
            padding: 0;
            box-sizing: border-box;
        }

        body {
            font-family: -apple-system, BlinkMacSystemFont, 'Segoe UI', Roboto, 'Helvetica Neue', Arial, sans-serif;
            line-height: 1.6;
            color: #333;
            background: #f5f5f5;
        }

        .header {
            background: #fff;
            border-bottom: 1px solid #e0e0e0;
            padding: 1rem 0;
            box-shadow: 0 2px 4px rgba(0,0,0,0.05);
        }

        .header-content {
            max-width: 1200px;
            margin: 0 auto;
            padding: 0 2rem;
            display: flex;
            justify-content: space-between;
            align-items: center;
        }

        .header h1 {
            font-size: 1.5rem;
            color: #2c3e50;
        }

        .nav {
            display: flex;
            gap: 1.5rem;
        }

        .nav a {
            color: #2c3e50;
            text-decoration: none;
            font-weight: 500;
            padding: 0.5rem 1rem;
            border-radius: 4px;
            transition: background 0.2s;
        }

        .nav a:hover {
            background: #f0f0f0;
        }

        .container {
            max-width: 1400px;
            margin: 2rem auto;
            padding: 0 2rem;
        }

        .content {
            background: #fff;
            border-radius: 8px;
            box-shadow: 0 1px 3px rgba(0,0,0,0.1);
            padding: 2rem;
        }

        h2 {
            font-size: 2rem;
            margin-bottom: 1rem;
            color: #2c3e50;
            border-bottom: 2px solid #e0e0e0;
            padding-bottom: 0.5rem;
        }

        .description {
            margin: 1.5rem 0;
            color: #666;
        }

        .pdf-container {
            width: 100%;
            height: 80vh;
            border: 1px solid #e0e0e0;
            border-radius: 4px;
            overflow: hidden;
        }

        .pdf-container embed {
            width: 100%;
            height: 100%;
        }

        .download-link {
            display: inline-block;
            margin-top: 1rem;
            padding: 0.75rem 1.5rem;
            background: #3498db;
            color: white;
            text-decoration: none;
            border-radius: 4px;
            transition: background 0.2s;
        }

        .download-link:hover {
            background: #2980b9;
        }

        .fallback {
            text-align: center;
            padding: 3rem;
            background: #f8f9fa;
            border-radius: 4px;
            margin-top: 1rem;
        }
    </style>
</head>
<body>
    <div class="header">
        <div class="header-content">
            <h1>Chebyshev Circles - Dependency Graph</h1>
            <nav class="nav">
                <a href="../">Home</a>
                <a href="../blueprint/">Blueprint</a>
                <a href="../docs/">API Docs</a>
                <a href="https://github.com/e-vergo/ChebyshevCircles">GitHub</a>
            </nav>
        </div>
    </div>

    <div class="container">
        <div class="content">
            <h2>Formalization Dependency Graph</h2>

            <div class="description">
                <p>
                    This dependency graph shows the relationships between all lemmas, theorems, and definitions
                    in the Chebyshev Circles formalization. Each node represents a formalized result, and edges
                    show which results depend on which others.
                </p>
                <p>
                    The graph provides a visual overview of the proof structure, making it easier to understand
                    how the main theorem is built up from foundational results.
                </p>
            </div>

            <a href="./blueprint.pdf" class="download-link" download>Download PDF</a>

            <div class="pdf-container">
                <embed src="./blueprint.pdf" type="application/pdf" />
            </div>

            <div class="fallback">
                <p>If the PDF doesn't display above, you can <a href="./blueprint.pdf" download>download it directly</a>.</p>
            </div>
        </div>
    </div>
</body>
</html>
EOF

echo "Created dependency graph visualization page at $OUTPUT_DIR/index.html"
