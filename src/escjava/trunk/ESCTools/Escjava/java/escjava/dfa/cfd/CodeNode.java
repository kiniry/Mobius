package escjava.dfa.cfd;

import java.io.ByteArrayOutputStream;
import java.io.IOException;
import java.io.Writer;

import javafe.ast.Expr;
import javafe.ast.PrettyPrint;
import javafe.util.Assert;
import escjava.ast.*;
import escjava.sp.SPVC;
import escjava.translate.GC;

/**
 * This class represents a node in control flow diagram that represent
 * a piece of code in program.
 */
public class CodeNode extends Node {

    //@ invariant code != null;
    GuardedCmd code;

    /**
     * Initializes a new instance of the Node class.
     * @param scope  vector variables representing scope of the new node
     */
    public CodeNode(/*@ non_null @*/GenericVarDeclVec scope,
                    /*@ non_null @*/GuardedCmd code) {
        super(scope);
        this.code = code;
    }


    //@ ensures \result == this.code;
    /*@ pure @*/public /*@ non_null @*/GuardedCmd getCode() {
        return this.code;
    }
    
    public void accept(/*@ non_null @*/NodeVisitor nodeVisitor) {
        nodeVisitor.visitCodeNode(this);
    }

   
    /**
     * Computes the stronest postcondition of this node, given a precondition.    
     * This implementation assumes that the code associated to this node is one of the commands ASSERT, ASSUME, SKIP.
     * @param pre precondition
     */
    public Expr computeSp(Expr pre) {
        int t = code.getTag();
          
        Assert.notFalse(
                t == TagConstants.ASSERTCMD || t == TagConstants.ASSUMECMD || t == TagConstants.SKIPCMD, 
                "The command associated to this code is not supported by this method (" + this.getCode() + ").");
       
        if (GC.isFalse(pre)) return GC.falselit;
        Expr post =  SPVC.computeN(code);
        Expr preAndPost = GC.and(pre, post);
        return preAndPost;
    }
    
    public String toString() {
        return "[code node: " + getCodeString() + "]";
     }
    
    private String getCodeString() {
        if (PrettyPrint.inst != null && PrettyPrint.inst instanceof EscPrettyPrint) {
            ByteArrayOutputStream bs = new ByteArrayOutputStream();
            ((EscPrettyPrint) PrettyPrint.inst).print(bs, 0, this.code);
            return bs.toString();

        } else
            return this.code.toString();
    }
    
     void printToDot(Writer dot) throws IOException {
         dot.write("" + hashCode() + " [label=\"" + getCodeString() + "\"];\n");      
    }


    public Node shallowCopy() {
        Node clone;
        clone = new CodeNode(this.scope.copy(), this.code);
        return clone;
    }



}
