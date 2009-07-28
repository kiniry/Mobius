#!/bin/sh

# generate functions for visitor class
cat TFunction.j | grep class | awk '{print $2}' | sed 's/^T\(.*\)/public\ void\ visitT\1\(\/\*@\ non_null\ @\*\/\ T\1\ n\)\{\}/g'
cat TLiteral.j | grep class | awk '{print $2}' | sed 's/^T\(.*\)/public\ void\ visitT\1\(\/\*@\ non_null\ @\*\/\ T\1\ n\)\{\}/g'

# generate functions for node class
cat TFunction.j | grep class | awk '{print $2}' | sed 's/^T\(.*\)/public\ void\ accept\(\/\*@\ non_null\ @\*\/\ TVisitor v\)\{\nv.visitT\1\(this\)\;\n\}/g'
cat TLiteral.j | grep class | awk '{print $2}' | sed 's/^T\(.*\)/public\ void\ accept\(\/\*@\ non_null\ @\*\/\ TVisitor v\)\{\nv.visitT\1\(this\)\;\n\}/g'
