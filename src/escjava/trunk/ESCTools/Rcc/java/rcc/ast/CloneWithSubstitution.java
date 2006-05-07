/* Copyright 2000, 2001, Compaq Computer Corporation */

package rcc.ast;

import javafe.util.Assert;
import javafe.util.Location;

import javafe.ast.*;


// Convention: unless otherwise noted, integer fields named "loc" refer
// to the location of the first character of the syntactic unit

public class CloneWithSubstitution extends CloneAST {
    protected MultipleSubstitution substitutions;
    protected CloneAST cloneNoSubs;
       
    public ASTNode  prep(ASTNode a, Object o) {
        ASTNode b = substitutions.substitute(a);
        return (ASTNode)(b==null?null:cloneNoSubs.clone(b,true));
    }
    
    
    public CloneWithSubstitution(MultipleSubstitution ms) {
        substitutions = ms;
        cloneNoSubs = new CloneAST();
    }
    

}
