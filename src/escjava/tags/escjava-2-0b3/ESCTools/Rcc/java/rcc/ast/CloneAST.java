/* Copyright 2000, 2001, Compaq Computer Corporation */

package rcc.ast;

import javafe.ast.ASTNode;
import javafe.ast.ClassDecl;
import javafe.ast.ConstructorInvocation;
import javafe.ast.Expr;
import javafe.ast.ExprVec;
import javafe.ast.FieldAccess;
import javafe.ast.FieldDecl;
import javafe.ast.InitBlock;
import javafe.ast.InterfaceDecl;
import javafe.ast.MethodInvocation;
import javafe.ast.NewInstanceExpr;
import javafe.ast.RoutineDecl;
import javafe.ast.TypeDecl;
import javafe.ast.VariableAccess;


// Convention: unless otherwise noted, integer fields named "loc" refer
// to the location of the first character of the syntactic unit

public class CloneAST extends CloneVisitorSuper {
    
    protected boolean cloneDecorations = true;

    public void setCloneDecorations(boolean b) {
        cloneDecorations = b;
    }

    public ASTNode finish(ASTNode a, Object o) {
        
        if (cloneDecorations) {
            cloneDecorations(a, (Boolean)o);
        } else {
            rcc.tc.FlowInsensitiveChecks.guardDecoration.set(a,null);
            rcc.tc.FlowInsensitiveChecks.requiresDecoration.set(a,null);
            rcc.tc.FlowInsensitiveChecks.elemGuardDecoration.set(a,null);
            rcc.tc.FlowInsensitiveChecks.threadLocalDecoration.set(a,null);
        }
        
        return a;
    }
    
    public Object visitClassDecl(ClassDecl y, Object o) {
       ClassDecl x = (ClassDecl)super.visitClassDecl(y,o);
               
        for (int i = 0; i < x.elems.size(); i++) {
            x.elems.elementAt(i).setParent(x);
        }
        return x;
   }

    public Object visitInterfaceDecl(InterfaceDecl y, Object o) {
       InterfaceDecl x = (InterfaceDecl)super.visitInterfaceDecl(y,o);
               
        for (int i = 0; i < x.elems.size(); i++) {
            x.elems.elementAt(i).setParent(x);
        }
        return x;
   }
       

    
    //@ ensures RES!=null
    public Object visitTypeDecl(TypeDecl y, Object o) {
        TypeDecl x = (TypeDecl)super.visitTypeDecl(y,o);
        if (!((Boolean)o).booleanValue()) {
            x.parent =null;
        }
        
        for (int i = 0; i < x.elems.size(); i++) {
            x.elems.elementAt(i).setParent(x);
        }

        return x;
    }
    
    //@ ensures RES!=f
    public Object visitRoutineDecl(RoutineDecl y, Object o) {
        RoutineDecl x = (RoutineDecl)super.visitRoutineDecl(y,o);  
        if (!((Boolean)o).booleanValue()) {
            x.parent =null;
            x.implicit = false;
        }
        return x;
    }
    
    
    //@ ensures RES!=f
    public Object visitInitBlock(InitBlock y, Object o) {
        InitBlock x = (InitBlock)super.visitInitBlock(y,o);  
        if (!((Boolean)o).booleanValue()) {
            x.parent =null;
        }
        return x;
    }
    
    
    //@ ensures RES!=f
    public Object visitFieldDecl(FieldDecl y, Object o) {
        FieldDecl x = (FieldDecl)super.visitFieldDecl(y,o);  
        if (!((Boolean)o).booleanValue()) {
            x.parent =null;
        }
        return x;
    }
    
    
    //@ ensures RES!=f
    public Object visitConstructorInvocation(ConstructorInvocation y, Object o) {
        ConstructorInvocation x = (ConstructorInvocation)super.visitConstructorInvocation(y,o);  
        if (!((Boolean)o).booleanValue()) {
            x.decl = null;
        }
        return x;
    }
    
    //@ ensures RES!=f
    public Object visitVariableAccess(VariableAccess y, Object o) {
        Object z = super.visitVariableAccess(y,o);
        if (!(z instanceof VariableAccess)) {
            return z;
        }
        
        VariableAccess x = (VariableAccess)z;  
        if (!((Boolean)o).booleanValue()) {
            x.decl = null;
        }
        return x;
    }
    
    //@ ensures RES!=f
    public Object visitNewInstanceExpr(NewInstanceExpr y, Object o) {
        NewInstanceExpr        x = (NewInstanceExpr)super.visitNewInstanceExpr(y,o);  
        if (!((Boolean)o).booleanValue()) {
            x.decl = null;
        }
        return x;
    }
    
    
    public Object visitFieldAccess(FieldAccess  y, Object o) {
        Object a = super.visitFieldAccess(y,o);
        if (!(a instanceof FieldAccess)) return a;
        FieldAccess x = (FieldAccess)a;  
        if (!((Boolean)o).booleanValue()) {
            x.decl = null;
        }
        return x;
    }
      //@ ensures RES!=f
    public Object visitMethodInvocation(MethodInvocation y, Object o) {
        MethodInvocation x = (MethodInvocation)super.visitMethodInvocation(y,o);  
        if (!((Boolean)o).booleanValue()) {
            x.decl = null;
        }
        return x;
    }
    
    
    
    public CloneAST() {
        // Do nothing
    }
    
    
    protected void  cloneDecorations(ASTNode x, Boolean b) {
        Object d[];
        
        if (x.getDecorations() != null) {
            d = new Object[x.getDecorations().length];
            java.lang.System.arraycopy(x.getDecorations(), 0, d, 0, x.getDecorations().length);
            for (int i=0; i<d.length; i++) {
                if (d[i] instanceof ASTNode && !(d[i] instanceof javafe.tc.TypeSig)) {
                    d[i] = (ASTNode)clone((ASTNode)d[i], b.booleanValue());
                } else   if (d[i] instanceof ExprVec) {
                    d[i] = clone((ExprVec)d[i], b.booleanValue());
                }
            }
        } else {
            d = null;
        }
        x.setDecorations(d);
    }
    
    
    public  ExprVec clone(ExprVec x, Boolean b) {
        return  clone(x, b.booleanValue());
    }
    
    public  ExprVec clone(ExprVec x, boolean b) {
        ExprVec _tempexpressions;
        if (x == null) {
            _tempexpressions = null; 
        } else {
            _tempexpressions = ExprVec.make(x.size());
            for (int i = 0; i < x.size(); i++) {
                _tempexpressions.insertElementAt((Expr)clone(x.elementAt(i), b),i);
            } 
        }
        return  _tempexpressions;
    }
    
    public Object  clone(ASTNode x,boolean b) {
        return (ASTNode)x.accept(this,new Boolean(b));
    }
}   

