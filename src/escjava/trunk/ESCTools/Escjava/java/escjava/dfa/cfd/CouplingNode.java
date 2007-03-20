package escjava.dfa.cfd;

import java.io.IOException;
import java.io.Writer;

import javafe.ast.Expr;
import escjava.ast.GenericVarDeclVec;

/**
 * This class represents a coupling node in control flow diagram.
 */
public class CouplingNode extends Node {
    public CouplingNode() {
        super(GenericVarDeclVec.make(0));
    }

    public void accept(NodeVisitor nodeVisitor) {
        nodeVisitor.visitCouplingNode(this);
    }

    public Expr computeSp(Expr pre) {
        return (Expr)pre.clone();
    }
    
    public String toString() {
     return "[coupling node]";
    }

    void printToDot(Writer dot) throws IOException {
        dot.write("" + hashCode() + "[shape=point, width=0.15];\n");
    }

    public Node shallowCopy() {
        return new CouplingNode();
    }

   
}


