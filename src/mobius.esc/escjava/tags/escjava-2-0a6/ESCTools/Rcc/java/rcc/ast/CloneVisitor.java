/* Copyright 2000, 2001, Compaq Computer Corporation */

package rcc.ast;


import java.util.Hashtable;

import javafe.ast.*;

import javafe.ast.Expr;
import javafe.util.Assert;
import javafe.util.Location;


// Convention: unless otherwise noted, integer fields named "loc"g refer
// to the locaction of the first character of the syntactic unit

//# TagBase javafe.tc.TagConstants.LAST_TAG + 1
//# VisitorRoot javafe.ast.Visitor
//# VisitorARRoot javafe.ast.VisitorArgResult

public class CloneVisitor  extends javafe.ast.CloneVisitor {
   public ASTNode prep(ASTNode y, Object o) { return null; }
public ASTNode finish(ASTNode y, Object o) { return y; }
//@ ensures RES!=null
   public Object visitAnOverview(AnOverview y, Object o) {
      return y.clone(); 
}
//@ ensures RES!=null
   public Object visitHoldsStmtPragma(HoldsStmtPragma y, Object o) {
      { ASTNode a=prep(y,o); if (a!=null) return a; }
      HoldsStmtPragma x = (HoldsStmtPragma)y.clone();  
      ExprVec _tempexpressions;
      if (x.expressions == null) {
         _tempexpressions = null; 
      } else {
      _tempexpressions = ExprVec.make(x.expressions.size());

      for (int i = 0; i < x.expressions.size(); i++) {
         _tempexpressions.insertElementAt((Expr)x.expressions.elementAt(i).accept(this,o),i);
      } 
   }
      x.expressions = _tempexpressions; 
return finish(x,y);
   }

//@ ensures RES!=null
   public Object visitRequiresModifierPragma(RequiresModifierPragma y, Object o) {
      { ASTNode a=prep(y,o); if (a!=null) return a; }
      RequiresModifierPragma x = (RequiresModifierPragma)y.clone();  
      ExprVec _tempexpressions;
      if (x.expressions == null) {
         _tempexpressions = null; 
      } else {
      _tempexpressions = ExprVec.make(x.expressions.size());

      for (int i = 0; i < x.expressions.size(); i++) {
         _tempexpressions.insertElementAt((Expr)x.expressions.elementAt(i).accept(this,o),i);
      } 
   }
      x.expressions = _tempexpressions; 
return finish(x,y);
   }

//@ ensures RES!=null
   public Object visitGuardedByModifierPragma(GuardedByModifierPragma y, Object o) {
      { ASTNode a=prep(y,o); if (a!=null) return a; }
      GuardedByModifierPragma x = (GuardedByModifierPragma)y.clone();  
      ExprVec _tempexpressions;
      if (x.expressions == null) {
         _tempexpressions = null; 
      } else {
      _tempexpressions = ExprVec.make(x.expressions.size());

      for (int i = 0; i < x.expressions.size(); i++) {
         _tempexpressions.insertElementAt((Expr)x.expressions.elementAt(i).accept(this,o),i);
      } 
   }
      x.expressions = _tempexpressions; 
return finish(x,y);
   }

//@ ensures RES!=null
   public Object visitThreadLocalStatusPragma(ThreadLocalStatusPragma y, Object o) {
      { ASTNode a=prep(y,o); if (a!=null) return a; }
      ThreadLocalStatusPragma x = (ThreadLocalStatusPragma)y.clone();  
return finish(x,y);
   }

//@ ensures RES!=null
   public Object visitReadOnlyModifierPragma(ReadOnlyModifierPragma y, Object o) {
      { ASTNode a=prep(y,o); if (a!=null) return a; }
      ReadOnlyModifierPragma x = (ReadOnlyModifierPragma)y.clone();  
return finish(x,y);
   }

//@ ensures RES!=null
   public Object visitArrayGuardModifierPragma(ArrayGuardModifierPragma y, Object o) {
      { ASTNode a=prep(y,o); if (a!=null) return a; }
      ArrayGuardModifierPragma x = (ArrayGuardModifierPragma)y.clone();  
      ExprVec _tempexpressions;
      if (x.expressions == null) {
         _tempexpressions = null; 
      } else {
      _tempexpressions = ExprVec.make(x.expressions.size());

      for (int i = 0; i < x.expressions.size(); i++) {
         _tempexpressions.insertElementAt((Expr)x.expressions.elementAt(i).accept(this,o),i);
      } 
   }
      x.expressions = _tempexpressions; 
return finish(x,y);
   }

//@ ensures RES!=null
   public Object visitNowarnPragma(NowarnPragma y, Object o) {
      { ASTNode a=prep(y,o); if (a!=null) return a; }
      NowarnPragma x = (NowarnPragma)y.clone();  
return finish(x,y);
   }

//@ ensures RES!=null
   public Object visitGenericArgumentPragma(GenericArgumentPragma y, Object o) {
      { ASTNode a=prep(y,o); if (a!=null) return a; }
      GenericArgumentPragma x = (GenericArgumentPragma)y.clone();  
      ExprVec _tempexpressions;
      if (x.expressions == null) {
         _tempexpressions = null; 
      } else {
      _tempexpressions = ExprVec.make(x.expressions.size());

      for (int i = 0; i < x.expressions.size(); i++) {
         _tempexpressions.insertElementAt((Expr)x.expressions.elementAt(i).accept(this,o),i);
      } 
   }
      x.expressions = _tempexpressions; 
return finish(x,y);
   }

//@ ensures RES!=null
   public Object visitGenericParameterPragma(GenericParameterPragma y, Object o) {
      { ASTNode a=prep(y,o); if (a!=null) return a; }
      GenericParameterPragma x = (GenericParameterPragma)y.clone();  
      FormalParaDeclVec _tempargs;
      if (x.args == null) {
         _tempargs = null; 
      } else {
      _tempargs = FormalParaDeclVec.make(x.args.size());

      for (int i = 0; i < x.args.size(); i++) {
         _tempargs.insertElementAt((FormalParaDecl)x.args.elementAt(i).accept(this,o),i);
      } 
   }
      x.args = _tempargs; 
return finish(x,y);
   }

//@ ensures RES!=null
   public Object visitGhostDeclPragma(GhostDeclPragma y, Object o) {
      { ASTNode a=prep(y,o); if (a!=null) return a; }
      GhostDeclPragma x = (GhostDeclPragma)y.clone();  
      FieldDecl _tempdecl = (FieldDecl)(x.decl == null ? null : x.decl.accept(this, o));
      x.decl = _tempdecl; 
return finish(x,y);
   }

}
