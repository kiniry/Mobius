package escjava.dfa.cfd;

import java.io.IOException;
import java.io.Writer;

import javafe.ast.Expr;
import escjava.ast.GenericVarDeclVec;

/**
 * This class represents an exception node in control flow diagram.
 */
public class ExceptionNode extends Node {
    public ExceptionNode () {
        super(GenericVarDeclVec.make(0));
    }

    public  void accept(NodeVisitor nodeVisitor) {
        nodeVisitor.visitExceptionNode(this);
    }
    
    public Expr computeSp(Expr pre) {
        return (Expr)pre.clone();
    }

    public String toString() {
        return "[exception node]";
       }

    void printToDot(Writer dot) throws IOException {
            dot.write("" + hashCode() + " [label=\"" + "RAISE" + "\"];\n");           
    }

    public Node shallowCopy() {
        return new ExceptionNode();
    }

}
