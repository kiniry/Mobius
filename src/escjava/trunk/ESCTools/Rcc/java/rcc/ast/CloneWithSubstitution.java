/* Copyright 2000, 2001, Compaq Computer Corporation */

package rcc.ast;

import java.util.Hashtable;

import javafe.util.Assert;
import javafe.util.Location;

import javafe.ast.*;


// Convention: unless otherwise noted, integer fields named "loc" refer
// to the location of the first character of the syntactic unit

public class CloneWithSubstitution extends CloneAST {
    protected MultipleSubstitution substitutions;
    protected CloneAST cloneNoSubs;
       
    public ASTNode  prep(ASTNode a, Object o) {
        /* DEBUG. Don't substitute the result of a substitution.
        if (dbgh.containsKey(a)) {
            System.out.println("Ouch!");
            new Exception().printStackTrace();
            System.out.println("=========");
            ((Exception)dbgh.get(a)).printStackTrace();
        }
        */
        ASTNode b = substitutions.substitute(a);
        /*
        if (a instanceof Expr) {
            dbg((Expr)a); System.out.println("->"); dbg((Expr)b);
        }
        */
        ASTNode result = (ASTNode)(b == null ? null : cloneNoSubs.clone(b, true));
        //if (result != null) dbgh.put(result, new Exception());
        return result;
    }
    
    
    public CloneWithSubstitution(MultipleSubstitution ms) {
        substitutions = ms;
        cloneNoSubs = new CloneAST();
    }
    

    // === Testing and debugging ===
    //private Hashtable dbgh = new Hashtable();
    
    private static void dbg(ExprVec exprs) {
        System.out.println(PrettyPrint.inst.toString(exprs));
    }
    
    private static void dbg(Expr expr) {
        System.out.println(PrettyPrint.inst.toString(expr));
    }
    
    private static void dbg(Type type) {
        System.out.println(PrettyPrint.inst.toString(type));
    }
}
