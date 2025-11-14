#!/bin/bash
# Create dependency graph redirect page
# This redirects to the interactive dependency graph in the blueprint

set -e

OUTPUT_DIR="$1"

if [ -z "$OUTPUT_DIR" ]; then
    echo "Usage: create_graph_page.sh <output_dir>"
    exit 1
fi

mkdir -p "$OUTPUT_DIR"

# Create redirect page to the blueprint's interactive dependency graph
cat > "$OUTPUT_DIR/index.html" << 'EOF'
<!DOCTYPE html>
<html lang="en">
<head>
    <meta charset="UTF-8">
    <meta http-equiv="refresh" content="0; url=../blueprint/dep_graph_document.html">
    <meta name="viewport" content="width=device-width, initial-scale=1.0">
    <title>Redirecting to Dependency Graph...</title>
    <style>
        * { margin: 0; padding: 0; box-sizing: border-box; }
        body {
            font-family: -apple-system, BlinkMacSystemFont, 'Segoe UI', Roboto, sans-serif;
            background: #f5f5f5;
            display: flex;
            align-items: center;
            justify-content: center;
            min-height: 100vh;
        }
        .message {
            background: #fff;
            border-radius: 8px;
            padding: 3rem;
            box-shadow: 0 2px 8px rgba(0,0,0,0.1);
            text-align: center;
            max-width: 500px;
        }
        h1 { color: #2c3e50; margin-bottom: 1rem; font-size: 1.5rem; }
        p { color: #666; margin-bottom: 1.5rem; }
        a {
            display: inline-block;
            padding: 0.75rem 1.5rem;
            background: #3498db;
            color: white;
            text-decoration: none;
            border-radius: 4px;
            transition: background 0.2s;
        }
        a:hover { background: #2980b9; }
    </style>
</head>
<body>
    <div class="message">
        <h1>Redirecting to Dependency Graph...</h1>
        <p>You are being redirected to the interactive dependency graph.</p>
        <p>If you are not redirected automatically, <a href="../blueprint/dep_graph_document.html">click here</a>.</p>
    </div>
</body>
</html>
EOF

echo "Created dependency graph redirect page at $OUTPUT_DIR/index.html"
