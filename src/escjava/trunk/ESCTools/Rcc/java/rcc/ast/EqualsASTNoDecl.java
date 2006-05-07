/* Copyright 2000, 2001, Compaq Computer Corporation */

package rcc.ast;

import javafe.util.Assert;
import javafe.util.Location;

import javafe.ast.*;

// Convention: unless otherwise noted, integer fields named "loc" refer
// to the location of the first character of the syntactic unit



public class EqualsASTNoDecl extends EqualityVisitorSuper {

    // get rid of parens, casts, etc.
    public Object prep(ASTNode y, Object o) {
        if (y instanceof CastExpr) {
            return new Boolean(equals(((CastExpr)y).expr, (ASTNode)o));
        }
        if (y instanceof ParenExpr) {
            return new Boolean(equals(((ParenExpr)y).expr, (ASTNode)o));
        }
        if (y instanceof CastExpr) {
            return new Boolean(equals(y, ((CastExpr)o).expr));
        }
        if (y instanceof ParenExpr) {
            return new Boolean(equals(y,((ParenExpr)o).expr));
        }
        return null;
    }
        
    
    public Object visitTypeName(TypeName y, Object o) {
        boolean x = true;  
        if (o instanceof TypeName) {
            TypeName z = (TypeName)o;
            if (!(y.tmodifiers == null && z.tmodifiers == null)) {
                if (y.tmodifiers != null && z.tmodifiers != null && (z.tmodifiers.size() == y.tmodifiers.size())) {
                    for (int i = 0; i < z.tmodifiers.size(); i++) {
                        x = x && ((Boolean)z.tmodifiers.elementAt(i).accept(this, y.tmodifiers.elementAt(i))).booleanValue();
                    }
                } else {
                    x = false;
                }
            }
            o = javafe.tc.TypeSig.getSig((TypeName)o);
            x = x && rcc.tc.TypeSig.getSig(y) == rcc.tc.TypeSig.getSig(z);
        } else if (o instanceof javafe.tc.TypeSig) {
            x = (rcc.tc.TypeSig.getSig(y) == o);
        } else {
            Assert.notFalse(false);
            x = false;
        }
        return new Boolean(x);
    }
    
    //@ ensures RES!=null
    public Object visitType(Type y, Object o) {
        if (y instanceof TypeName) y =  javafe.tc.TypeSig.getSig((TypeName)y);
        if (o instanceof TypeName) o =  javafe.tc.TypeSig.getSig((TypeName)o);
        if (y instanceof javafe.tc.TypeSig && o instanceof javafe.tc.TypeSig) {

            
           return new Boolean(y == o);
        }
        Assert.notFalse(false); return o; 
    }
    
    
    //@ ensures RES!=null
    public boolean equals (ExprVec a, ExprVec b) {
        
        if (a.size()!=b.size()) {
            return false;
        }
        for (int i=0; i<a.size(); i++) {
            if (!equals(a.elementAt(i),b.elementAt(i))) {
                return false;
                
            }
            
        }
        return  true;
        
    }
    
    
    
    public boolean subset (ExprVec a, ExprVec b) {
        
        
    outer:
        for (int i=0; i<a.size(); i++) {
            for (int j = 0; j<b.size(); j++) {
                if (equals(a.elementAt(i),b.elementAt(j))) {
                    continue outer;
                }
            }
            return false;
        }
        return  true;
    }   

    public boolean contains(ExprVec a, Expr expr) {
        for (int j = 0; j<a.size(); j++) {
            if (equals(a.elementAt(j),expr)) {
                return true;
            }
        }
        return false;
    }
    
    public boolean equalsSet (ExprVec a, ExprVec b) {
        
        
    outer:
        for (int i=0; i<a.size(); i++) {
            for (int j = 0; j<b.size(); j++) {
                if (equals(a.elementAt(i),b.elementAt(j))) {
                    continue outer;
                }
            }
            return false;
        }
    outer2:
        for (int i=0; i<b.size(); i++) {
            for (int j = 0; j<a.size(); j++) {
                if (equals(a.elementAt(j),b.elementAt(i))) {
                    continue outer2;
                }
            }
            return false;
        }
        
        return  true;
        
    }
    
    
    public boolean  equals(ASTNode x,ASTNode y) {
        return ((Boolean)x.accept(this,y)).booleanValue();
    }
    
}
