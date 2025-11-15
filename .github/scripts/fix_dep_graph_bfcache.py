#!/usr/bin/env python3
"""
Fix dependency graph to handle browser back/forward cache (bfcache).
When navigating back, the page is restored from cache but d3-graphviz doesn't re-initialize.
This wraps the initialization in a function and calls it on pageshow from cache.
"""
import sys
import re

def fix_dep_graph_bfcache(filepath):
    with open(filepath, 'r') as f:
        content = f.read()
    
    # Find the graph initialization code (from graphContainer assignment to .on("end", interactive))
    pattern = r'(const graphContainer = d3\.select\("#graph"\);.*?\.on\("end", interactive\);)'
    match = re.search(pattern, content, re.DOTALL)
    
    if not match:
        print(f"ERROR: Could not find graph initialization code in {filepath}", file=sys.stderr)
        return False
    
    init_code = match.group(1)
    
    # Wrap in a function and add pageshow event listener
    replacement = f'''function initializeGraph() {{
  // Clear any existing graph content
  d3.select("#graph").selectAll("*").remove();
  
  {init_code}
}}

// Initialize on load
initializeGraph();

// Re-initialize when page is restored from bfcache
window.addEventListener('pageshow', function(event) {{
  if (event.persisted) {{
    console.log('Page restored from cache, re-initializing graph');
    initializeGraph();
  }}
}});'''
    
    # Replace the original code
    new_content = content.replace(init_code, replacement)
    
    # Write back
    with open(filepath, 'w') as f:
        f.write(new_content)
    
    print(f"Successfully patched {filepath} for bfcache handling")
    return True

if __name__ == '__main__':
    if len(sys.argv) != 2:
        print(f"Usage: {sys.argv[0]} <dep_graph_document.html>", file=sys.stderr)
        sys.exit(1)
    
    filepath = sys.argv[1]
    success = fix_dep_graph_bfcache(filepath)
    sys.exit(0 if success else 1)
