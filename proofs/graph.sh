#!/bin/sh

project_file=_CoqProject
name=dependency_graph
dot_file=${name}.dot
pdf_file=${name}.pdf

# Generate "dot" file with module dependencies
# `coqdep` is a standard utility distributed with Coq system
coqdep -f ${project_file} -dumpgraph ${dot_file} > /dev/null

# Generate a pdf with toposorted graph from the dot file
# `dot` utility is distributed with graphviz utility collection
# One can usually install it using a package manager like homebrew on macOS:
#    brew install graphviz
dot -Tpdf ${dot_file} -o ${pdf_file}
