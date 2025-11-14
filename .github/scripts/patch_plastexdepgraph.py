#!/usr/bin/env python3
"""
Patch plastexdepgraph to fix TypeError: unhashable type: 'lemma'

This patch makes plasTeX theorem environment nodes hashable by their id attribute,
allowing them to be used in sets and as dictionary keys.
"""

import sys
from pathlib import Path

def find_depgraph_file():
    """Find the depgraph.py file in the installed packages."""
    import plastexdepgraph
    pkg_path = Path(plastexdepgraph.__file__).parent
    return pkg_path / 'Packages' / 'depgraph.py'

def apply_patch():
    """Apply the monkey-patch to make nodes hashable."""
    depgraph_file = find_depgraph_file()

    if not depgraph_file.exists():
        print(f"ERROR: Could not find {depgraph_file}")
        sys.exit(1)

    content = depgraph_file.read_text()

    # Check if already patched
    if '_hash_patched' in content:
        print("Patch already applied, skipping.")
        return

    # Find the makegraph function and add the monkey-patch before graph.nodes = set(nodes)
    patch_code = '''        # Monkey-patch node classes to make them hashable if they aren't already
        for node in nodes:
            node_class = node.__class__
            if not hasattr(node_class, '_hash_patched'):
                def _node_hash(self):
                    return hash(self.id)
                def _node_eq(self, other):
                    if not isinstance(other, self.__class__.__bases__[0]):
                        return False
                    return self.id == other.id
                node_class.__hash__ = _node_hash
                node_class.__eq__ = _node_eq
                node_class._hash_patched = True
'''

    # Replace the line where graph.nodes is set
    old_code = '        graph = DepGraph()\n        graph.document = document\n        graph.nodes = set(nodes)'
    new_code = '        graph = DepGraph()\n        graph.document = document\n' + patch_code + '        graph.nodes = set(nodes)'

    if old_code not in content:
        print("ERROR: Could not find target code to patch")
        sys.exit(1)

    content = content.replace(old_code, new_code)
    depgraph_file.write_text(content)
    print(f"Successfully patched {depgraph_file}")

if __name__ == '__main__':
    apply_patch()
