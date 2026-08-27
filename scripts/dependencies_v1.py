# based on https://github.com/AmosNico/validator

import os
import graphviz

BASE = "https://github.com/m4lvin/lean4-pdl/tree/main/"
EXCLUDE = set(['.lake', 'docbuild',".github",".devcontainer",".vscode","Bml","Unused","Pdl.lean"])

def add_node(dot, path, name, label) :
    with open(path, "r") as f:
        content = f.read()
        if "sorry" in content:
            dot.node(name, label=f"{label}?", color="red", href=f"{BASE}{name}.html")
        else:
            dot.node(name, label=f"{label}✓", color="green", href=f"{BASE}{name}.html")

def dependencies(dot, path, name) :
    with open(path, "r") as f:
        lines = f.readlines()
        for line in lines:
            if "import Pdl." in line:
                imported_module = line.split("import ")[1].strip()
                imported_file = imported_module.replace(".", "/")
                dot.edge(imported_file, name)

# Create a Graphviz Digraph object
dot = graphviz.Digraph(comment='Lean Files Dependencies')
dot.attr(ranksep = '0.6')
dot.attr(nodesep = '0.6')

def traverse(root, dot_path) :
    _, dirs, files = next(os.walk(root))
    for file in files:
        if file in EXCLUDE : continue
        if file.endswith(".lean"):
            path = os.path.join(root, file)
            name = path[2:-5]
            add_node(dot_path, path, name, file[:-5])
            dependencies(dot, path, name)

    for dir in dirs :
        if dir in EXCLUDE : continue
        path = os.path.join(root, dir)
        dot_sub = graphviz.Digraph(name=f"cluster{path}")
        dot_sub.attr(label = dir)
        dot_sub.attr(style = "rounded")
        traverse(path, dot_sub)
        dot_path.subgraph(dot_sub)

traverse(".", dot)

# Render the graph to SVG and PNG formats
dot.render('dependencies', format='svg')
dot.render('dependencies', format='png')
