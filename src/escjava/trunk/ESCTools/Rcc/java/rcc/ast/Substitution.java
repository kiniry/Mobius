/* Copyright 2000, 2001, Compaq Computer Corporation */

package rcc.ast;

import javafe.util.Assert;
import javafe.util.Location;

import javafe.ast.*;

public class Substitution {
    public ASTNode match;
    public ASTNode replace;

    public  Substitution(ASTNode m,ASTNode r) {
        match = m;
        replace = r;
    }

    public String  toString() {
        return "("+match+"->"+replace+")";
    }
    
}
