/* Copyright 2000, 2001, Compaq Computer Corporation */


package rcc.ast;

import javafe.ast.*;

import javafe.util.Assert;
import javafe.util.Location;


// Convention: unless otherwise noted, integer fields named "loc" refer
// to the location of the first character of the syntactic unit

public class EqualityVisitorSuper  extends VisitorArgResult {
   public Object prep(ASTNode y, Object o) { return null; }
   //@ ensures RES!=null
   public Object visitASTNode(ASTNode y, Object o) {
   Assert.notFalse(false); return o; 
}
   //@ ensures RES!=null
   public Object visitCompilationUnit(CompilationUnit y, Object o) {
      Boolean _tmp = (Boolean)prep(y,o);
      if (_tmp!=null) return _tmp;
      if (!(o instanceof CompilationUnit)) return new Boolean(false);
      boolean x = true;  
      CompilationUnit z = (CompilationUnit)o;
      x = x && (y.pkgName == null && z.pkgName == null ||  (y.pkgName != null && z.pkgName != null && ((Boolean)(y.pkgName.accept(this, z.pkgName))).booleanValue()));
      if (!(y.lexicalPragmas == null && z.lexicalPragmas == null)) {
         if (y.lexicalPragmas != null && z.lexicalPragmas != null && (z.lexicalPragmas.size() == y.lexicalPragmas.size())) {
            for (int i = 0; i < z.lexicalPragmas.size(); i++) {
               x = x && ((Boolean)z.lexicalPragmas.elementAt(i).accept(this, y.lexicalPragmas.elementAt(i))).booleanValue();
            }
         } else {
            x = false;
         }
      }
      if (!(y.imports == null && z.imports == null)) {
         if (y.imports != null && z.imports != null && (z.imports.size() == y.imports.size())) {
            for (int i = 0; i < z.imports.size(); i++) {
               x = x && ((Boolean)z.imports.elementAt(i).accept(this, y.imports.elementAt(i))).booleanValue();
            }
         } else {
            x = false;
         }
      }
      if (!(y.elems == null && z.elems == null)) {
         if (y.elems != null && z.elems != null && (z.elems.size() == y.elems.size())) {
            for (int i = 0; i < z.elems.size(); i++) {
               x = x && ((Boolean)z.elems.elementAt(i).accept(this, y.elems.elementAt(i))).booleanValue();
            }
         } else {
            x = false;
         }
      }
      return new Boolean(x);
   }

   //@ ensures RES!=null
   public Object visitImportDecl(ImportDecl y, Object o) {
   Assert.notFalse(false); return o; 
}
   //@ ensures RES!=null
   public Object visitSingleTypeImportDecl(SingleTypeImportDecl y, Object o) {
      Boolean _tmp = (Boolean)prep(y,o);
      if (_tmp!=null) return _tmp;
      if (!(o instanceof SingleTypeImportDecl)) return new Boolean(false);
      boolean x = true;  
      SingleTypeImportDecl z = (SingleTypeImportDecl)o;
      x = x && (y.typeName == null && z.typeName == null ||  (y.typeName != null && z.typeName != null && ((Boolean)(y.typeName.accept(this, z.typeName))).booleanValue()));
      return new Boolean(x);
   }

   //@ ensures RES!=null
   public Object visitOnDemandImportDecl(OnDemandImportDecl y, Object o) {
      Boolean _tmp = (Boolean)prep(y,o);
      if (_tmp!=null) return _tmp;
      if (!(o instanceof OnDemandImportDecl)) return new Boolean(false);
      boolean x = true;  
      OnDemandImportDecl z = (OnDemandImportDecl)o;
      x = x && (y.pkgName == null && z.pkgName == null ||  (y.pkgName != null && z.pkgName != null && ((Boolean)(y.pkgName.accept(this, z.pkgName))).booleanValue()));
      return new Boolean(x);
   }

   //@ ensures RES!=null
   public Object visitTypeDecl(TypeDecl y, Object o) {
   Assert.notFalse(false); return o; 
}
   //@ ensures RES!=null
   public Object visitClassDecl(ClassDecl y, Object o) {
      Boolean _tmp = (Boolean)prep(y,o);
      if (_tmp!=null) return _tmp;
      if (!(o instanceof ClassDecl)) return new Boolean(false);
      boolean x = true;  
      ClassDecl z = (ClassDecl)o;
      x = x && (z.modifiers == y.modifiers);
      if (!(y.pmodifiers == null && z.pmodifiers == null)) {
         if (y.pmodifiers != null && z.pmodifiers != null && (z.pmodifiers.size() == y.pmodifiers.size())) {
            for (int i = 0; i < z.pmodifiers.size(); i++) {
               x = x && ((Boolean)z.pmodifiers.elementAt(i).accept(this, y.pmodifiers.elementAt(i))).booleanValue();
            }
         } else {
            x = false;
         }
      }
      x = x && (z.id == y.id);
      if (!(y.tmodifiers == null && z.tmodifiers == null)) {
         if (y.tmodifiers != null && z.tmodifiers != null && (z.tmodifiers.size() == y.tmodifiers.size())) {
            for (int i = 0; i < z.tmodifiers.size(); i++) {
               x = x && ((Boolean)z.tmodifiers.elementAt(i).accept(this, y.tmodifiers.elementAt(i))).booleanValue();
            }
         } else {
            x = false;
         }
      }
      if (!(y.superInterfaces == null && z.superInterfaces == null)) {
         if (y.superInterfaces != null && z.superInterfaces != null && (z.superInterfaces.size() == y.superInterfaces.size())) {
            for (int i = 0; i < z.superInterfaces.size(); i++) {
               x = x && ((Boolean)z.superInterfaces.elementAt(i).accept(this, y.superInterfaces.elementAt(i))).booleanValue();
            }
         } else {
            x = false;
         }
      }
      if (!(y.elems == null && z.elems == null)) {
         if (y.elems != null && z.elems != null && (z.elems.size() == y.elems.size())) {
            for (int i = 0; i < z.elems.size(); i++) {
               x = x && ((Boolean)z.elems.elementAt(i).accept(this, y.elems.elementAt(i))).booleanValue();
            }
         } else {
            x = false;
         }
      }
      x = x && (y.superClass == null && z.superClass == null ||  (y.superClass != null && z.superClass != null && ((Boolean)(y.superClass.accept(this, z.superClass))).booleanValue()));
      return new Boolean(x);
   }

   //@ ensures RES!=null
   public Object visitInterfaceDecl(InterfaceDecl y, Object o) {
      Boolean _tmp = (Boolean)prep(y,o);
      if (_tmp!=null) return _tmp;
      if (!(o instanceof InterfaceDecl)) return new Boolean(false);
      boolean x = true;  
      InterfaceDecl z = (InterfaceDecl)o;
      x = x && (z.modifiers == y.modifiers);
      if (!(y.pmodifiers == null && z.pmodifiers == null)) {
         if (y.pmodifiers != null && z.pmodifiers != null && (z.pmodifiers.size() == y.pmodifiers.size())) {
            for (int i = 0; i < z.pmodifiers.size(); i++) {
               x = x && ((Boolean)z.pmodifiers.elementAt(i).accept(this, y.pmodifiers.elementAt(i))).booleanValue();
            }
         } else {
            x = false;
         }
      }
      x = x && (z.id == y.id);
      if (!(y.tmodifiers == null && z.tmodifiers == null)) {
         if (y.tmodifiers != null && z.tmodifiers != null && (z.tmodifiers.size() == y.tmodifiers.size())) {
            for (int i = 0; i < z.tmodifiers.size(); i++) {
               x = x && ((Boolean)z.tmodifiers.elementAt(i).accept(this, y.tmodifiers.elementAt(i))).booleanValue();
            }
         } else {
            x = false;
         }
      }
      if (!(y.superInterfaces == null && z.superInterfaces == null)) {
         if (y.superInterfaces != null && z.superInterfaces != null && (z.superInterfaces.size() == y.superInterfaces.size())) {
            for (int i = 0; i < z.superInterfaces.size(); i++) {
               x = x && ((Boolean)z.superInterfaces.elementAt(i).accept(this, y.superInterfaces.elementAt(i))).booleanValue();
            }
         } else {
            x = false;
         }
      }
      if (!(y.elems == null && z.elems == null)) {
         if (y.elems != null && z.elems != null && (z.elems.size() == y.elems.size())) {
            for (int i = 0; i < z.elems.size(); i++) {
               x = x && ((Boolean)z.elems.elementAt(i).accept(this, y.elems.elementAt(i))).booleanValue();
            }
         } else {
            x = false;
         }
      }
      return new Boolean(x);
   }

   //@ ensures RES!=null
   public Object visitRoutineDecl(RoutineDecl y, Object o) {
   Assert.notFalse(false); return o; 
}
   //@ ensures RES!=null
   public Object visitConstructorDecl(ConstructorDecl y, Object o) {
      Boolean _tmp = (Boolean)prep(y,o);
      if (_tmp!=null) return _tmp;
      if (!(o instanceof ConstructorDecl)) return new Boolean(false);
      boolean x = true;  
      ConstructorDecl z = (ConstructorDecl)o;
      x = x && (z.modifiers == y.modifiers);
      if (!(y.pmodifiers == null && z.pmodifiers == null)) {
         if (y.pmodifiers != null && z.pmodifiers != null && (z.pmodifiers.size() == y.pmodifiers.size())) {
            for (int i = 0; i < z.pmodifiers.size(); i++) {
               x = x && ((Boolean)z.pmodifiers.elementAt(i).accept(this, y.pmodifiers.elementAt(i))).booleanValue();
            }
         } else {
            x = false;
         }
      }
      if (!(y.tmodifiers == null && z.tmodifiers == null)) {
         if (y.tmodifiers != null && z.tmodifiers != null && (z.tmodifiers.size() == y.tmodifiers.size())) {
            for (int i = 0; i < z.tmodifiers.size(); i++) {
               x = x && ((Boolean)z.tmodifiers.elementAt(i).accept(this, y.tmodifiers.elementAt(i))).booleanValue();
            }
         } else {
            x = false;
         }
      }
      if (!(y.args == null && z.args == null)) {
         if (y.args != null && z.args != null && (z.args.size() == y.args.size())) {
            for (int i = 0; i < z.args.size(); i++) {
               x = x && ((Boolean)z.args.elementAt(i).accept(this, y.args.elementAt(i))).booleanValue();
            }
         } else {
            x = false;
         }
      }
      if (!(y.raises == null && z.raises == null)) {
         if (y.raises != null && z.raises != null && (z.raises.size() == y.raises.size())) {
            for (int i = 0; i < z.raises.size(); i++) {
               x = x && ((Boolean)z.raises.elementAt(i).accept(this, y.raises.elementAt(i))).booleanValue();
            }
         } else {
            x = false;
         }
      }
      x = x && (y.body == null && z.body == null ||  (y.body != null && z.body != null && ((Boolean)(y.body.accept(this, z.body))).booleanValue()));
      return new Boolean(x);
   }

   //@ ensures RES!=null
   public Object visitMethodDecl(MethodDecl y, Object o) {
      Boolean _tmp = (Boolean)prep(y,o);
      if (_tmp!=null) return _tmp;
      if (!(o instanceof MethodDecl)) return new Boolean(false);
      boolean x = true;  
      MethodDecl z = (MethodDecl)o;
      x = x && (z.modifiers == y.modifiers);
      if (!(y.pmodifiers == null && z.pmodifiers == null)) {
         if (y.pmodifiers != null && z.pmodifiers != null && (z.pmodifiers.size() == y.pmodifiers.size())) {
            for (int i = 0; i < z.pmodifiers.size(); i++) {
               x = x && ((Boolean)z.pmodifiers.elementAt(i).accept(this, y.pmodifiers.elementAt(i))).booleanValue();
            }
         } else {
            x = false;
         }
      }
      if (!(y.tmodifiers == null && z.tmodifiers == null)) {
         if (y.tmodifiers != null && z.tmodifiers != null && (z.tmodifiers.size() == y.tmodifiers.size())) {
            for (int i = 0; i < z.tmodifiers.size(); i++) {
               x = x && ((Boolean)z.tmodifiers.elementAt(i).accept(this, y.tmodifiers.elementAt(i))).booleanValue();
            }
         } else {
            x = false;
         }
      }
      if (!(y.args == null && z.args == null)) {
         if (y.args != null && z.args != null && (z.args.size() == y.args.size())) {
            for (int i = 0; i < z.args.size(); i++) {
               x = x && ((Boolean)z.args.elementAt(i).accept(this, y.args.elementAt(i))).booleanValue();
            }
         } else {
            x = false;
         }
      }
      if (!(y.raises == null && z.raises == null)) {
         if (y.raises != null && z.raises != null && (z.raises.size() == y.raises.size())) {
            for (int i = 0; i < z.raises.size(); i++) {
               x = x && ((Boolean)z.raises.elementAt(i).accept(this, y.raises.elementAt(i))).booleanValue();
            }
         } else {
            x = false;
         }
      }
      x = x && (y.body == null && z.body == null ||  (y.body != null && z.body != null && ((Boolean)(y.body.accept(this, z.body))).booleanValue()));
      x = x && (z.id == y.id);
      x = x && (y.returnType == null && z.returnType == null ||  (y.returnType != null && z.returnType != null && ((Boolean)(y.returnType.accept(this, z.returnType))).booleanValue()));
      return new Boolean(x);
   }

   //@ ensures RES!=null
   public Object visitInitBlock(InitBlock y, Object o) {
      Boolean _tmp = (Boolean)prep(y,o);
      if (_tmp!=null) return _tmp;
      if (!(o instanceof InitBlock)) return new Boolean(false);
      boolean x = true;  
      InitBlock z = (InitBlock)o;
      x = x && (z.modifiers == y.modifiers);
      if (!(y.pmodifiers == null && z.pmodifiers == null)) {
         if (y.pmodifiers != null && z.pmodifiers != null && (z.pmodifiers.size() == y.pmodifiers.size())) {
            for (int i = 0; i < z.pmodifiers.size(); i++) {
               x = x && ((Boolean)z.pmodifiers.elementAt(i).accept(this, y.pmodifiers.elementAt(i))).booleanValue();
            }
         } else {
            x = false;
         }
      }
      x = x && (y.block == null && z.block == null ||  (y.block != null && z.block != null && ((Boolean)(y.block.accept(this, z.block))).booleanValue()));
      return new Boolean(x);
   }

   //@ ensures RES!=null
   public Object visitTypeDeclElemPragma(TypeDeclElemPragma y, Object o) {
   Assert.notFalse(false); return o; 
}
   //@ ensures RES!=null
   public Object visitGenericVarDecl(GenericVarDecl y, Object o) {
   Assert.notFalse(false); return o; 
}
   //@ ensures RES!=null
   public Object visitLocalVarDecl(LocalVarDecl y, Object o) {
      Boolean _tmp = (Boolean)prep(y,o);
      if (_tmp!=null) return _tmp;
      if (!(o instanceof LocalVarDecl)) return new Boolean(false);
      boolean x = true;  
      LocalVarDecl z = (LocalVarDecl)o;
      x = x && (z.modifiers == y.modifiers);
      if (!(y.pmodifiers == null && z.pmodifiers == null)) {
         if (y.pmodifiers != null && z.pmodifiers != null && (z.pmodifiers.size() == y.pmodifiers.size())) {
            for (int i = 0; i < z.pmodifiers.size(); i++) {
               x = x && ((Boolean)z.pmodifiers.elementAt(i).accept(this, y.pmodifiers.elementAt(i))).booleanValue();
            }
         } else {
            x = false;
         }
      }
      x = x && (z.id == y.id);
      x = x && (y.type == null && z.type == null ||  (y.type != null && z.type != null && ((Boolean)(y.type.accept(this, z.type))).booleanValue()));
      x = x && (y.init == null && z.init == null ||  (y.init != null && z.init != null && ((Boolean)(y.init.accept(this, z.init))).booleanValue()));
      return new Boolean(x);
   }

   //@ ensures RES!=null
   public Object visitFieldDecl(FieldDecl y, Object o) {
      Boolean _tmp = (Boolean)prep(y,o);
      if (_tmp!=null) return _tmp;
      if (!(o instanceof FieldDecl)) return new Boolean(false);
      boolean x = true;  
      FieldDecl z = (FieldDecl)o;
      x = x && (z.modifiers == y.modifiers);
      if (!(y.pmodifiers == null && z.pmodifiers == null)) {
         if (y.pmodifiers != null && z.pmodifiers != null && (z.pmodifiers.size() == y.pmodifiers.size())) {
            for (int i = 0; i < z.pmodifiers.size(); i++) {
               x = x && ((Boolean)z.pmodifiers.elementAt(i).accept(this, y.pmodifiers.elementAt(i))).booleanValue();
            }
         } else {
            x = false;
         }
      }
      x = x && (z.id == y.id);
      x = x && (y.type == null && z.type == null ||  (y.type != null && z.type != null && ((Boolean)(y.type.accept(this, z.type))).booleanValue()));
      x = x && (y.init == null && z.init == null ||  (y.init != null && z.init != null && ((Boolean)(y.init.accept(this, z.init))).booleanValue()));
      return new Boolean(x);
   }

   //@ ensures RES!=null
   public Object visitFormalParaDecl(FormalParaDecl y, Object o) {
      Boolean _tmp = (Boolean)prep(y,o);
      if (_tmp!=null) return _tmp;
      if (!(o instanceof FormalParaDecl)) return new Boolean(false);
      boolean x = true;  
      FormalParaDecl z = (FormalParaDecl)o;
      x = x && (z.modifiers == y.modifiers);
      if (!(y.pmodifiers == null && z.pmodifiers == null)) {
         if (y.pmodifiers != null && z.pmodifiers != null && (z.pmodifiers.size() == y.pmodifiers.size())) {
            for (int i = 0; i < z.pmodifiers.size(); i++) {
               x = x && ((Boolean)z.pmodifiers.elementAt(i).accept(this, y.pmodifiers.elementAt(i))).booleanValue();
            }
         } else {
            x = false;
         }
      }
      x = x && (z.id == y.id);
      x = x && (y.type == null && z.type == null ||  (y.type != null && z.type != null && ((Boolean)(y.type.accept(this, z.type))).booleanValue()));
      return new Boolean(x);
   }

   //@ ensures RES!=null
   public Object visitStmt(Stmt y, Object o) {
   Assert.notFalse(false); return o; 
}
   //@ ensures RES!=null
   public Object visitGenericBlockStmt(GenericBlockStmt y, Object o) {
   Assert.notFalse(false); return o; 
}
   //@ ensures RES!=null
   public Object visitBlockStmt(BlockStmt y, Object o) {
      Boolean _tmp = (Boolean)prep(y,o);
      if (_tmp!=null) return _tmp;
      if (!(o instanceof BlockStmt)) return new Boolean(false);
      boolean x = true;  
      BlockStmt z = (BlockStmt)o;
      if (!(y.stmts == null && z.stmts == null)) {
         if (y.stmts != null && z.stmts != null && (z.stmts.size() == y.stmts.size())) {
            for (int i = 0; i < z.stmts.size(); i++) {
               x = x && ((Boolean)z.stmts.elementAt(i).accept(this, y.stmts.elementAt(i))).booleanValue();
            }
         } else {
            x = false;
         }
      }
      return new Boolean(x);
   }

   //@ ensures RES!=null
   public Object visitSwitchStmt(SwitchStmt y, Object o) {
      Boolean _tmp = (Boolean)prep(y,o);
      if (_tmp!=null) return _tmp;
      if (!(o instanceof SwitchStmt)) return new Boolean(false);
      boolean x = true;  
      SwitchStmt z = (SwitchStmt)o;
      if (!(y.stmts == null && z.stmts == null)) {
         if (y.stmts != null && z.stmts != null && (z.stmts.size() == y.stmts.size())) {
            for (int i = 0; i < z.stmts.size(); i++) {
               x = x && ((Boolean)z.stmts.elementAt(i).accept(this, y.stmts.elementAt(i))).booleanValue();
            }
         } else {
            x = false;
         }
      }
      x = x && (y.expr == null && z.expr == null ||  (y.expr != null && z.expr != null && ((Boolean)(y.expr.accept(this, z.expr))).booleanValue()));
      return new Boolean(x);
   }

   //@ ensures RES!=null
   public Object visitVarDeclStmt(VarDeclStmt y, Object o) {
      Boolean _tmp = (Boolean)prep(y,o);
      if (_tmp!=null) return _tmp;
      if (!(o instanceof VarDeclStmt)) return new Boolean(false);
      boolean x = true;  
      VarDeclStmt z = (VarDeclStmt)o;
      x = x && (y.decl == null && z.decl == null ||  (y.decl != null && z.decl != null && ((Boolean)(y.decl.accept(this, z.decl))).booleanValue()));
      return new Boolean(x);
   }

   //@ ensures RES!=null
   public Object visitClassDeclStmt(ClassDeclStmt y, Object o) {
      Boolean _tmp = (Boolean)prep(y,o);
      if (_tmp!=null) return _tmp;
      if (!(o instanceof ClassDeclStmt)) return new Boolean(false);
      boolean x = true;  
      ClassDeclStmt z = (ClassDeclStmt)o;
      x = x && (y.decl == null && z.decl == null ||  (y.decl != null && z.decl != null && ((Boolean)(y.decl.accept(this, z.decl))).booleanValue()));
      return new Boolean(x);
   }

   //@ ensures RES!=null
   public Object visitWhileStmt(WhileStmt y, Object o) {
      Boolean _tmp = (Boolean)prep(y,o);
      if (_tmp!=null) return _tmp;
      if (!(o instanceof WhileStmt)) return new Boolean(false);
      boolean x = true;  
      WhileStmt z = (WhileStmt)o;
      x = x && (y.expr == null && z.expr == null ||  (y.expr != null && z.expr != null && ((Boolean)(y.expr.accept(this, z.expr))).booleanValue()));
      x = x && (y.stmt == null && z.stmt == null ||  (y.stmt != null && z.stmt != null && ((Boolean)(y.stmt.accept(this, z.stmt))).booleanValue()));
      return new Boolean(x);
   }

   //@ ensures RES!=null
   public Object visitDoStmt(DoStmt y, Object o) {
      Boolean _tmp = (Boolean)prep(y,o);
      if (_tmp!=null) return _tmp;
      if (!(o instanceof DoStmt)) return new Boolean(false);
      boolean x = true;  
      DoStmt z = (DoStmt)o;
      x = x && (y.expr == null && z.expr == null ||  (y.expr != null && z.expr != null && ((Boolean)(y.expr.accept(this, z.expr))).booleanValue()));
      x = x && (y.stmt == null && z.stmt == null ||  (y.stmt != null && z.stmt != null && ((Boolean)(y.stmt.accept(this, z.stmt))).booleanValue()));
      return new Boolean(x);
   }

   //@ ensures RES!=null
   public Object visitSynchronizeStmt(SynchronizeStmt y, Object o) {
      Boolean _tmp = (Boolean)prep(y,o);
      if (_tmp!=null) return _tmp;
      if (!(o instanceof SynchronizeStmt)) return new Boolean(false);
      boolean x = true;  
      SynchronizeStmt z = (SynchronizeStmt)o;
      x = x && (y.expr == null && z.expr == null ||  (y.expr != null && z.expr != null && ((Boolean)(y.expr.accept(this, z.expr))).booleanValue()));
      x = x && (y.stmt == null && z.stmt == null ||  (y.stmt != null && z.stmt != null && ((Boolean)(y.stmt.accept(this, z.stmt))).booleanValue()));
      return new Boolean(x);
   }

   //@ ensures RES!=null
   public Object visitEvalStmt(EvalStmt y, Object o) {
      Boolean _tmp = (Boolean)prep(y,o);
      if (_tmp!=null) return _tmp;
      if (!(o instanceof EvalStmt)) return new Boolean(false);
      boolean x = true;  
      EvalStmt z = (EvalStmt)o;
      x = x && (y.expr == null && z.expr == null ||  (y.expr != null && z.expr != null && ((Boolean)(y.expr.accept(this, z.expr))).booleanValue()));
      return new Boolean(x);
   }

   //@ ensures RES!=null
   public Object visitReturnStmt(ReturnStmt y, Object o) {
      Boolean _tmp = (Boolean)prep(y,o);
      if (_tmp!=null) return _tmp;
      if (!(o instanceof ReturnStmt)) return new Boolean(false);
      boolean x = true;  
      ReturnStmt z = (ReturnStmt)o;
      x = x && (y.expr == null && z.expr == null ||  (y.expr != null && z.expr != null && ((Boolean)(y.expr.accept(this, z.expr))).booleanValue()));
      return new Boolean(x);
   }

   //@ ensures RES!=null
   public Object visitThrowStmt(ThrowStmt y, Object o) {
      Boolean _tmp = (Boolean)prep(y,o);
      if (_tmp!=null) return _tmp;
      if (!(o instanceof ThrowStmt)) return new Boolean(false);
      boolean x = true;  
      ThrowStmt z = (ThrowStmt)o;
      x = x && (y.expr == null && z.expr == null ||  (y.expr != null && z.expr != null && ((Boolean)(y.expr.accept(this, z.expr))).booleanValue()));
      return new Boolean(x);
   }

   //@ ensures RES!=null
   public Object visitBranchStmt(BranchStmt y, Object o) {
   Assert.notFalse(false); return o; 
}
   //@ ensures RES!=null
   public Object visitBreakStmt(BreakStmt y, Object o) {
      Boolean _tmp = (Boolean)prep(y,o);
      if (_tmp!=null) return _tmp;
      if (!(o instanceof BreakStmt)) return new Boolean(false);
      boolean x = true;  
      BreakStmt z = (BreakStmt)o;
      x = x && (z.label == y.label);
      return new Boolean(x);
   }

   //@ ensures RES!=null
   public Object visitContinueStmt(ContinueStmt y, Object o) {
      Boolean _tmp = (Boolean)prep(y,o);
      if (_tmp!=null) return _tmp;
      if (!(o instanceof ContinueStmt)) return new Boolean(false);
      boolean x = true;  
      ContinueStmt z = (ContinueStmt)o;
      x = x && (z.label == y.label);
      return new Boolean(x);
   }

   //@ ensures RES!=null
   public Object visitLabelStmt(LabelStmt y, Object o) {
      Boolean _tmp = (Boolean)prep(y,o);
      if (_tmp!=null) return _tmp;
      if (!(o instanceof LabelStmt)) return new Boolean(false);
      boolean x = true;  
      LabelStmt z = (LabelStmt)o;
      x = x && (z.label == y.label);
      x = x && (y.stmt == null && z.stmt == null ||  (y.stmt != null && z.stmt != null && ((Boolean)(y.stmt.accept(this, z.stmt))).booleanValue()));
      return new Boolean(x);
   }

   //@ ensures RES!=null
   public Object visitIfStmt(IfStmt y, Object o) {
      Boolean _tmp = (Boolean)prep(y,o);
      if (_tmp!=null) return _tmp;
      if (!(o instanceof IfStmt)) return new Boolean(false);
      boolean x = true;  
      IfStmt z = (IfStmt)o;
      x = x && (y.expr == null && z.expr == null ||  (y.expr != null && z.expr != null && ((Boolean)(y.expr.accept(this, z.expr))).booleanValue()));
      x = x && (y.thn == null && z.thn == null ||  (y.thn != null && z.thn != null && ((Boolean)(y.thn.accept(this, z.thn))).booleanValue()));
      x = x && (y.els == null && z.els == null ||  (y.els != null && z.els != null && ((Boolean)(y.els.accept(this, z.els))).booleanValue()));
      return new Boolean(x);
   }

   //@ ensures RES!=null
   public Object visitForStmt(ForStmt y, Object o) {
      Boolean _tmp = (Boolean)prep(y,o);
      if (_tmp!=null) return _tmp;
      if (!(o instanceof ForStmt)) return new Boolean(false);
      boolean x = true;  
      ForStmt z = (ForStmt)o;
      if (!(y.forInit == null && z.forInit == null)) {
         if (y.forInit != null && z.forInit != null && (z.forInit.size() == y.forInit.size())) {
            for (int i = 0; i < z.forInit.size(); i++) {
               x = x && ((Boolean)z.forInit.elementAt(i).accept(this, y.forInit.elementAt(i))).booleanValue();
            }
         } else {
            x = false;
         }
      }
      x = x && (y.test == null && z.test == null ||  (y.test != null && z.test != null && ((Boolean)(y.test.accept(this, z.test))).booleanValue()));
      if (!(y.forUpdate == null && z.forUpdate == null)) {
         if (y.forUpdate != null && z.forUpdate != null && (z.forUpdate.size() == y.forUpdate.size())) {
            for (int i = 0; i < z.forUpdate.size(); i++) {
               x = x && ((Boolean)z.forUpdate.elementAt(i).accept(this, y.forUpdate.elementAt(i))).booleanValue();
            }
         } else {
            x = false;
         }
      }
      x = x && (y.body == null && z.body == null ||  (y.body != null && z.body != null && ((Boolean)(y.body.accept(this, z.body))).booleanValue()));
      return new Boolean(x);
   }

   //@ ensures RES!=null
   public Object visitSkipStmt(SkipStmt y, Object o) {
      Boolean _tmp = (Boolean)prep(y,o);
      if (_tmp!=null) return _tmp;
      if (!(o instanceof SkipStmt)) return new Boolean(false);
      boolean x = true;  
      SkipStmt z = (SkipStmt)o;
      return new Boolean(x);
   }

   //@ ensures RES!=null
   public Object visitSwitchLabel(SwitchLabel y, Object o) {
      Boolean _tmp = (Boolean)prep(y,o);
      if (_tmp!=null) return _tmp;
      if (!(o instanceof SwitchLabel)) return new Boolean(false);
      boolean x = true;  
      SwitchLabel z = (SwitchLabel)o;
      x = x && (y.expr == null && z.expr == null ||  (y.expr != null && z.expr != null && ((Boolean)(y.expr.accept(this, z.expr))).booleanValue()));
      return new Boolean(x);
   }

   //@ ensures RES!=null
   public Object visitTryFinallyStmt(TryFinallyStmt y, Object o) {
      Boolean _tmp = (Boolean)prep(y,o);
      if (_tmp!=null) return _tmp;
      if (!(o instanceof TryFinallyStmt)) return new Boolean(false);
      boolean x = true;  
      TryFinallyStmt z = (TryFinallyStmt)o;
      x = x && (y.tryClause == null && z.tryClause == null ||  (y.tryClause != null && z.tryClause != null && ((Boolean)(y.tryClause.accept(this, z.tryClause))).booleanValue()));
      x = x && (y.finallyClause == null && z.finallyClause == null ||  (y.finallyClause != null && z.finallyClause != null && ((Boolean)(y.finallyClause.accept(this, z.finallyClause))).booleanValue()));
      return new Boolean(x);
   }

   //@ ensures RES!=null
   public Object visitTryCatchStmt(TryCatchStmt y, Object o) {
      Boolean _tmp = (Boolean)prep(y,o);
      if (_tmp!=null) return _tmp;
      if (!(o instanceof TryCatchStmt)) return new Boolean(false);
      boolean x = true;  
      TryCatchStmt z = (TryCatchStmt)o;
      x = x && (y.tryClause == null && z.tryClause == null ||  (y.tryClause != null && z.tryClause != null && ((Boolean)(y.tryClause.accept(this, z.tryClause))).booleanValue()));
      if (!(y.catchClauses == null && z.catchClauses == null)) {
         if (y.catchClauses != null && z.catchClauses != null && (z.catchClauses.size() == y.catchClauses.size())) {
            for (int i = 0; i < z.catchClauses.size(); i++) {
               x = x && ((Boolean)z.catchClauses.elementAt(i).accept(this, y.catchClauses.elementAt(i))).booleanValue();
            }
         } else {
            x = false;
         }
      }
      return new Boolean(x);
   }

   //@ ensures RES!=null
   public Object visitStmtPragma(StmtPragma y, Object o) {
   Assert.notFalse(false); return o; 
}
   //@ ensures RES!=null
   public Object visitConstructorInvocation(ConstructorInvocation y, Object o) {
      Boolean _tmp = (Boolean)prep(y,o);
      if (_tmp!=null) return _tmp;
      if (!(o instanceof ConstructorInvocation)) return new Boolean(false);
      boolean x = true;  
      ConstructorInvocation z = (ConstructorInvocation)o;
      x = x && (z.superCall == y.superCall);
      x = x && (y.enclosingInstance == null && z.enclosingInstance == null ||  (y.enclosingInstance != null && z.enclosingInstance != null && ((Boolean)(y.enclosingInstance.accept(this, z.enclosingInstance))).booleanValue()));
      if (!(y.args == null && z.args == null)) {
         if (y.args != null && z.args != null && (z.args.size() == y.args.size())) {
            for (int i = 0; i < z.args.size(); i++) {
               x = x && ((Boolean)z.args.elementAt(i).accept(this, y.args.elementAt(i))).booleanValue();
            }
         } else {
            x = false;
         }
      }
      return new Boolean(x);
   }

   //@ ensures RES!=null
   public Object visitCatchClause(CatchClause y, Object o) {
      Boolean _tmp = (Boolean)prep(y,o);
      if (_tmp!=null) return _tmp;
      if (!(o instanceof CatchClause)) return new Boolean(false);
      boolean x = true;  
      CatchClause z = (CatchClause)o;
      x = x && (y.arg == null && z.arg == null ||  (y.arg != null && z.arg != null && ((Boolean)(y.arg.accept(this, z.arg))).booleanValue()));
      x = x && (y.body == null && z.body == null ||  (y.body != null && z.body != null && ((Boolean)(y.body.accept(this, z.body))).booleanValue()));
      return new Boolean(x);
   }

   //@ ensures RES!=null
   public Object visitVarInit(VarInit y, Object o) {
   Assert.notFalse(false); return o; 
}
   //@ ensures RES!=null
   public Object visitArrayInit(ArrayInit y, Object o) {
      Boolean _tmp = (Boolean)prep(y,o);
      if (_tmp!=null) return _tmp;
      if (!(o instanceof ArrayInit)) return new Boolean(false);
      boolean x = true;  
      ArrayInit z = (ArrayInit)o;
      if (!(y.elems == null && z.elems == null)) {
         if (y.elems != null && z.elems != null && (z.elems.size() == y.elems.size())) {
            for (int i = 0; i < z.elems.size(); i++) {
               x = x && ((Boolean)z.elems.elementAt(i).accept(this, y.elems.elementAt(i))).booleanValue();
            }
         } else {
            x = false;
         }
      }
      return new Boolean(x);
   }

   //@ ensures RES!=null
   public Object visitExpr(Expr y, Object o) {
   Assert.notFalse(false); return o; 
}
   //@ ensures RES!=null
   public Object visitThisExpr(ThisExpr y, Object o) {
      Boolean _tmp = (Boolean)prep(y,o);
      if (_tmp!=null) return _tmp;
      if (!(o instanceof ThisExpr)) return new Boolean(false);
      boolean x = true;  
      ThisExpr z = (ThisExpr)o;
      x = x && (y.classPrefix == null && z.classPrefix == null ||  (y.classPrefix != null && z.classPrefix != null && ((Boolean)(y.classPrefix.accept(this, z.classPrefix))).booleanValue()));
      return new Boolean(x);
   }

   //@ ensures RES!=null
   public Object visitLiteralExpr(LiteralExpr y, Object o) {
      Boolean _tmp = (Boolean)prep(y,o);
      if (_tmp!=null) return _tmp;
      if (!(o instanceof LiteralExpr)) return new Boolean(false);
      boolean x = true;  
      LiteralExpr z = (LiteralExpr)o;
      x = x && (z.tag == y.tag);
      x = x && ((z.value == null && y.value == null) || (z.value!= null && y.value != null && z.value.equals(y.value)));
      return new Boolean(x);
   }

   //@ ensures RES!=null
   public Object visitArrayRefExpr(ArrayRefExpr y, Object o) {
      Boolean _tmp = (Boolean)prep(y,o);
      if (_tmp!=null) return _tmp;
      if (!(o instanceof ArrayRefExpr)) return new Boolean(false);
      boolean x = true;  
      ArrayRefExpr z = (ArrayRefExpr)o;
      x = x && (y.array == null && z.array == null ||  (y.array != null && z.array != null && ((Boolean)(y.array.accept(this, z.array))).booleanValue()));
      x = x && (y.index == null && z.index == null ||  (y.index != null && z.index != null && ((Boolean)(y.index.accept(this, z.index))).booleanValue()));
      return new Boolean(x);
   }

   //@ ensures RES!=null
   public Object visitNewInstanceExpr(NewInstanceExpr y, Object o) {
      Boolean _tmp = (Boolean)prep(y,o);
      if (_tmp!=null) return _tmp;
      if (!(o instanceof NewInstanceExpr)) return new Boolean(false);
      boolean x = true;  
      NewInstanceExpr z = (NewInstanceExpr)o;
      x = x && (y.enclosingInstance == null && z.enclosingInstance == null ||  (y.enclosingInstance != null && z.enclosingInstance != null && ((Boolean)(y.enclosingInstance.accept(this, z.enclosingInstance))).booleanValue()));
      x = x && (y.type == null && z.type == null ||  (y.type != null && z.type != null && ((Boolean)(y.type.accept(this, z.type))).booleanValue()));
      if (!(y.args == null && z.args == null)) {
         if (y.args != null && z.args != null && (z.args.size() == y.args.size())) {
            for (int i = 0; i < z.args.size(); i++) {
               x = x && ((Boolean)z.args.elementAt(i).accept(this, y.args.elementAt(i))).booleanValue();
            }
         } else {
            x = false;
         }
      }
      x = x && (y.anonDecl == null && z.anonDecl == null ||  (y.anonDecl != null && z.anonDecl != null && ((Boolean)(y.anonDecl.accept(this, z.anonDecl))).booleanValue()));
      return new Boolean(x);
   }

   //@ ensures RES!=null
   public Object visitNewArrayExpr(NewArrayExpr y, Object o) {
      Boolean _tmp = (Boolean)prep(y,o);
      if (_tmp!=null) return _tmp;
      if (!(o instanceof NewArrayExpr)) return new Boolean(false);
      boolean x = true;  
      NewArrayExpr z = (NewArrayExpr)o;
      x = x && (y.type == null && z.type == null ||  (y.type != null && z.type != null && ((Boolean)(y.type.accept(this, z.type))).booleanValue()));
      if (!(y.dims == null && z.dims == null)) {
         if (y.dims != null && z.dims != null && (z.dims.size() == y.dims.size())) {
            for (int i = 0; i < z.dims.size(); i++) {
               x = x && ((Boolean)z.dims.elementAt(i).accept(this, y.dims.elementAt(i))).booleanValue();
            }
         } else {
            x = false;
         }
      }
      x = x && (y.init == null && z.init == null ||  (y.init != null && z.init != null && ((Boolean)(y.init.accept(this, z.init))).booleanValue()));
      if (!(y.locOpenBrackets == null && z.locOpenBrackets == null)) {
         if (y.locOpenBrackets != null && z.locOpenBrackets != null && z.locOpenBrackets.length == y.locOpenBrackets.length) { 
            for (int i = 0; i < z.locOpenBrackets.length; i++) {
               x = x && (z.locOpenBrackets[i]==y.locOpenBrackets[i]);
            }
         } else {
            x = false;
         }
      }
      return new Boolean(x);
   }

   //@ ensures RES!=null
   public Object visitCondExpr(CondExpr y, Object o) {
      Boolean _tmp = (Boolean)prep(y,o);
      if (_tmp!=null) return _tmp;
      if (!(o instanceof CondExpr)) return new Boolean(false);
      boolean x = true;  
      CondExpr z = (CondExpr)o;
      x = x && (y.test == null && z.test == null ||  (y.test != null && z.test != null && ((Boolean)(y.test.accept(this, z.test))).booleanValue()));
      x = x && (y.thn == null && z.thn == null ||  (y.thn != null && z.thn != null && ((Boolean)(y.thn.accept(this, z.thn))).booleanValue()));
      x = x && (y.els == null && z.els == null ||  (y.els != null && z.els != null && ((Boolean)(y.els.accept(this, z.els))).booleanValue()));
      return new Boolean(x);
   }

   //@ ensures RES!=null
   public Object visitInstanceOfExpr(InstanceOfExpr y, Object o) {
      Boolean _tmp = (Boolean)prep(y,o);
      if (_tmp!=null) return _tmp;
      if (!(o instanceof InstanceOfExpr)) return new Boolean(false);
      boolean x = true;  
      InstanceOfExpr z = (InstanceOfExpr)o;
      x = x && (y.expr == null && z.expr == null ||  (y.expr != null && z.expr != null && ((Boolean)(y.expr.accept(this, z.expr))).booleanValue()));
      x = x && (y.type == null && z.type == null ||  (y.type != null && z.type != null && ((Boolean)(y.type.accept(this, z.type))).booleanValue()));
      return new Boolean(x);
   }

   //@ ensures RES!=null
   public Object visitCastExpr(CastExpr y, Object o) {
      Boolean _tmp = (Boolean)prep(y,o);
      if (_tmp!=null) return _tmp;
      if (!(o instanceof CastExpr)) return new Boolean(false);
      boolean x = true;  
      CastExpr z = (CastExpr)o;
      x = x && (y.expr == null && z.expr == null ||  (y.expr != null && z.expr != null && ((Boolean)(y.expr.accept(this, z.expr))).booleanValue()));
      x = x && (y.type == null && z.type == null ||  (y.type != null && z.type != null && ((Boolean)(y.type.accept(this, z.type))).booleanValue()));
      return new Boolean(x);
   }

   //@ ensures RES!=null
   public Object visitBinaryExpr(BinaryExpr y, Object o) {
      Boolean _tmp = (Boolean)prep(y,o);
      if (_tmp!=null) return _tmp;
      if (!(o instanceof BinaryExpr)) return new Boolean(false);
      boolean x = true;  
      BinaryExpr z = (BinaryExpr)o;
      x = x && (z.op == y.op);
      x = x && (y.left == null && z.left == null ||  (y.left != null && z.left != null && ((Boolean)(y.left.accept(this, z.left))).booleanValue()));
      x = x && (y.right == null && z.right == null ||  (y.right != null && z.right != null && ((Boolean)(y.right.accept(this, z.right))).booleanValue()));
      return new Boolean(x);
   }

   //@ ensures RES!=null
   public Object visitUnaryExpr(UnaryExpr y, Object o) {
      Boolean _tmp = (Boolean)prep(y,o);
      if (_tmp!=null) return _tmp;
      if (!(o instanceof UnaryExpr)) return new Boolean(false);
      boolean x = true;  
      UnaryExpr z = (UnaryExpr)o;
      x = x && (z.op == y.op);
      x = x && (y.expr == null && z.expr == null ||  (y.expr != null && z.expr != null && ((Boolean)(y.expr.accept(this, z.expr))).booleanValue()));
      return new Boolean(x);
   }

   //@ ensures RES!=null
   public Object visitParenExpr(ParenExpr y, Object o) {
      Boolean _tmp = (Boolean)prep(y,o);
      if (_tmp!=null) return _tmp;
      if (!(o instanceof ParenExpr)) return new Boolean(false);
      boolean x = true;  
      ParenExpr z = (ParenExpr)o;
      x = x && (y.expr == null && z.expr == null ||  (y.expr != null && z.expr != null && ((Boolean)(y.expr.accept(this, z.expr))).booleanValue()));
      return new Boolean(x);
   }

   //@ ensures RES!=null
   public Object visitAmbiguousVariableAccess(AmbiguousVariableAccess y, Object o) {
      Boolean _tmp = (Boolean)prep(y,o);
      if (_tmp!=null) return _tmp;
      if (!(o instanceof AmbiguousVariableAccess)) return new Boolean(false);
      boolean x = true;  
      AmbiguousVariableAccess z = (AmbiguousVariableAccess)o;
      x = x && (y.name == null && z.name == null ||  (y.name != null && z.name != null && ((Boolean)(y.name.accept(this, z.name))).booleanValue()));
      return new Boolean(x);
   }

   //@ ensures RES!=null
   public Object visitVariableAccess(VariableAccess y, Object o) {
      Boolean _tmp = (Boolean)prep(y,o);
      if (_tmp!=null) return _tmp;
      if (!(o instanceof VariableAccess)) return new Boolean(false);
      boolean x = true;  
      VariableAccess z = (VariableAccess)o;
      x = x && (z.id == y.id);
      return new Boolean(x);
   }

   //@ ensures RES!=null
   public Object visitFieldAccess(FieldAccess y, Object o) {
      Boolean _tmp = (Boolean)prep(y,o);
      if (_tmp!=null) return _tmp;
      if (!(o instanceof FieldAccess)) return new Boolean(false);
      boolean x = true;  
      FieldAccess z = (FieldAccess)o;
      x = x && (y.od == null && z.od == null ||  (y.od != null && z.od != null && ((Boolean)(y.od.accept(this, z.od))).booleanValue()));
      x = x && (z.id == y.id);
      return new Boolean(x);
   }

   //@ ensures RES!=null
   public Object visitAmbiguousMethodInvocation(AmbiguousMethodInvocation y, Object o) {
      Boolean _tmp = (Boolean)prep(y,o);
      if (_tmp!=null) return _tmp;
      if (!(o instanceof AmbiguousMethodInvocation)) return new Boolean(false);
      boolean x = true;  
      AmbiguousMethodInvocation z = (AmbiguousMethodInvocation)o;
      x = x && (y.name == null && z.name == null ||  (y.name != null && z.name != null && ((Boolean)(y.name.accept(this, z.name))).booleanValue()));
      if (!(y.tmodifiers == null && z.tmodifiers == null)) {
         if (y.tmodifiers != null && z.tmodifiers != null && (z.tmodifiers.size() == y.tmodifiers.size())) {
            for (int i = 0; i < z.tmodifiers.size(); i++) {
               x = x && ((Boolean)z.tmodifiers.elementAt(i).accept(this, y.tmodifiers.elementAt(i))).booleanValue();
            }
         } else {
            x = false;
         }
      }
      if (!(y.args == null && z.args == null)) {
         if (y.args != null && z.args != null && (z.args.size() == y.args.size())) {
            for (int i = 0; i < z.args.size(); i++) {
               x = x && ((Boolean)z.args.elementAt(i).accept(this, y.args.elementAt(i))).booleanValue();
            }
         } else {
            x = false;
         }
      }
      return new Boolean(x);
   }

   //@ ensures RES!=null
   public Object visitMethodInvocation(MethodInvocation y, Object o) {
      Boolean _tmp = (Boolean)prep(y,o);
      if (_tmp!=null) return _tmp;
      if (!(o instanceof MethodInvocation)) return new Boolean(false);
      boolean x = true;  
      MethodInvocation z = (MethodInvocation)o;
      x = x && (y.od == null && z.od == null ||  (y.od != null && z.od != null && ((Boolean)(y.od.accept(this, z.od))).booleanValue()));
      x = x && (z.id == y.id);
      if (!(y.tmodifiers == null && z.tmodifiers == null)) {
         if (y.tmodifiers != null && z.tmodifiers != null && (z.tmodifiers.size() == y.tmodifiers.size())) {
            for (int i = 0; i < z.tmodifiers.size(); i++) {
               x = x && ((Boolean)z.tmodifiers.elementAt(i).accept(this, y.tmodifiers.elementAt(i))).booleanValue();
            }
         } else {
            x = false;
         }
      }
      if (!(y.args == null && z.args == null)) {
         if (y.args != null && z.args != null && (z.args.size() == y.args.size())) {
            for (int i = 0; i < z.args.size(); i++) {
               x = x && ((Boolean)z.args.elementAt(i).accept(this, y.args.elementAt(i))).booleanValue();
            }
         } else {
            x = false;
         }
      }
      return new Boolean(x);
   }

   //@ ensures RES!=null
   public Object visitClassLiteral(ClassLiteral y, Object o) {
      Boolean _tmp = (Boolean)prep(y,o);
      if (_tmp!=null) return _tmp;
      if (!(o instanceof ClassLiteral)) return new Boolean(false);
      boolean x = true;  
      ClassLiteral z = (ClassLiteral)o;
      x = x && (y.type == null && z.type == null ||  (y.type != null && z.type != null && ((Boolean)(y.type.accept(this, z.type))).booleanValue()));
      return new Boolean(x);
   }

   //@ ensures RES!=null
   public Object visitObjectDesignator(ObjectDesignator y, Object o) {
   Assert.notFalse(false); return o; 
}
   //@ ensures RES!=null
   public Object visitExprObjectDesignator(ExprObjectDesignator y, Object o) {
      Boolean _tmp = (Boolean)prep(y,o);
      if (_tmp!=null) return _tmp;
      if (!(o instanceof ExprObjectDesignator)) return new Boolean(false);
      boolean x = true;  
      ExprObjectDesignator z = (ExprObjectDesignator)o;
      x = x && (y.expr == null && z.expr == null ||  (y.expr != null && z.expr != null && ((Boolean)(y.expr.accept(this, z.expr))).booleanValue()));
      return new Boolean(x);
   }

   //@ ensures RES!=null
   public Object visitTypeObjectDesignator(TypeObjectDesignator y, Object o) {
      Boolean _tmp = (Boolean)prep(y,o);
      if (_tmp!=null) return _tmp;
      if (!(o instanceof TypeObjectDesignator)) return new Boolean(false);
      boolean x = true;  
      TypeObjectDesignator z = (TypeObjectDesignator)o;
      x = x && (y.type == null && z.type == null ||  (y.type != null && z.type != null && ((Boolean)(y.type.accept(this, z.type))).booleanValue()));
      return new Boolean(x);
   }

   //@ ensures RES!=null
   public Object visitSuperObjectDesignator(SuperObjectDesignator y, Object o) {
      Boolean _tmp = (Boolean)prep(y,o);
      if (_tmp!=null) return _tmp;
      if (!(o instanceof SuperObjectDesignator)) return new Boolean(false);
      boolean x = true;  
      SuperObjectDesignator z = (SuperObjectDesignator)o;
      return new Boolean(x);
   }

   //@ ensures RES!=null
   public Object visitType(Type y, Object o) {
   Assert.notFalse(false); return o; 
}
   //@ ensures RES!=null
   public Object visitPrimitiveType(PrimitiveType y, Object o) {
      Boolean _tmp = (Boolean)prep(y,o);
      if (_tmp!=null) return _tmp;
      if (!(o instanceof PrimitiveType)) return new Boolean(false);
      boolean x = true;  
      PrimitiveType z = (PrimitiveType)o;
      if (!(y.tmodifiers == null && z.tmodifiers == null)) {
         if (y.tmodifiers != null && z.tmodifiers != null && (z.tmodifiers.size() == y.tmodifiers.size())) {
            for (int i = 0; i < z.tmodifiers.size(); i++) {
               x = x && ((Boolean)z.tmodifiers.elementAt(i).accept(this, y.tmodifiers.elementAt(i))).booleanValue();
            }
         } else {
            x = false;
         }
      }
      x = x && (z.tag == y.tag);
      return new Boolean(x);
   }

   //@ ensures RES!=null
   public Object visitTypeName(TypeName y, Object o) {
      Boolean _tmp = (Boolean)prep(y,o);
      if (_tmp!=null) return _tmp;
      if (!(o instanceof TypeName)) return new Boolean(false);
      boolean x = true;  
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
      x = x && (y.name == null && z.name == null ||  (y.name != null && z.name != null && ((Boolean)(y.name.accept(this, z.name))).booleanValue()));
      return new Boolean(x);
   }

   //@ ensures RES!=null
   public Object visitArrayType(ArrayType y, Object o) {
      Boolean _tmp = (Boolean)prep(y,o);
      if (_tmp!=null) return _tmp;
      if (!(o instanceof ArrayType)) return new Boolean(false);
      boolean x = true;  
      ArrayType z = (ArrayType)o;
      if (!(y.tmodifiers == null && z.tmodifiers == null)) {
         if (y.tmodifiers != null && z.tmodifiers != null && (z.tmodifiers.size() == y.tmodifiers.size())) {
            for (int i = 0; i < z.tmodifiers.size(); i++) {
               x = x && ((Boolean)z.tmodifiers.elementAt(i).accept(this, y.tmodifiers.elementAt(i))).booleanValue();
            }
         } else {
            x = false;
         }
      }
      x = x && (y.elemType == null && z.elemType == null ||  (y.elemType != null && z.elemType != null && ((Boolean)(y.elemType.accept(this, z.elemType))).booleanValue()));
      return new Boolean(x);
   }

   //@ ensures RES!=null
   public Object visitName(Name y, Object o) {
   Assert.notFalse(false); return o; 
}
   //@ ensures RES!=null
   public Object visitSimpleName(SimpleName y, Object o) {
      Boolean _tmp = (Boolean)prep(y,o);
      if (_tmp!=null) return _tmp;
      if (!(o instanceof SimpleName)) return new Boolean(false);
      boolean x = true;  
      SimpleName z = (SimpleName)o;
      x = x && (z.id == y.id);
      return new Boolean(x);
   }

   //@ ensures RES!=null
   public Object visitCompoundName(CompoundName y, Object o) {
      Boolean _tmp = (Boolean)prep(y,o);
      if (_tmp!=null) return _tmp;
      if (!(o instanceof CompoundName)) return new Boolean(false);
      boolean x = true;  
      CompoundName z = (CompoundName)o;
      x = x && (z.ids == y.ids);
      if (!(y.locIds == null && z.locIds == null)) {
         if (y.locIds != null && z.locIds != null && z.locIds.length == y.locIds.length) { 
            for (int i = 0; i < z.locIds.length; i++) {
               x = x && (z.locIds[i]==y.locIds[i]);
            }
         } else {
            x = false;
         }
      }
      if (!(y.locDots == null && z.locDots == null)) {
         if (y.locDots != null && z.locDots != null && z.locDots.length == y.locDots.length) { 
            for (int i = 0; i < z.locDots.length; i++) {
               x = x && (z.locDots[i]==y.locDots[i]);
            }
         } else {
            x = false;
         }
      }
      return new Boolean(x);
   }

   //@ ensures RES!=null
   public Object visitModifierPragma(ModifierPragma y, Object o) {
   Assert.notFalse(false); return o; 
}
   //@ ensures RES!=null
   public Object visitLexicalPragma(LexicalPragma y, Object o) {
   Assert.notFalse(false); return o; 
}
   //@ ensures RES!=null
    //   public Object visitTypeModifierPragma(TypeDeclModifierPragma y, Object o) {
    //Assert.notFalse(false); return o; 
    //}
   //@ ensures RES!=null
   public Object visitTypeModifierPragma(TypeModifierPragma y, Object o) {
   Assert.notFalse(false); return o; 
}


   //@ ensures RES!=null
   public Object visitAnOverview(AnOverview y, Object o) {
   Assert.notFalse(false); return o; 
}
   //@ ensures RES!=null
   public Object visitHoldsStmtPragma(HoldsStmtPragma y, Object o) {
      Boolean _tmp = (Boolean)prep(y,o);
      if (_tmp!=null) return _tmp;
      if (!(o instanceof HoldsStmtPragma)) return new Boolean(false);
      boolean x = true;  
      HoldsStmtPragma z = (HoldsStmtPragma)o;
      if (!(y.expressions == null && z.expressions == null)) {
         if (y.expressions != null && z.expressions != null && (z.expressions.size() == y.expressions.size())) {
            for (int i = 0; i < z.expressions.size(); i++) {
               x = x && ((Boolean)z.expressions.elementAt(i).accept(this, y.expressions.elementAt(i))).booleanValue();
            }
         } else {
            x = false;
         }
      }
      return new Boolean(x);
   }

   //@ ensures RES!=null
   public Object visitRequiresModifierPragma(RequiresModifierPragma y, Object o) {
      Boolean _tmp = (Boolean)prep(y,o);
      if (_tmp!=null) return _tmp;
      if (!(o instanceof RequiresModifierPragma)) return new Boolean(false);
      boolean x = true;  
      RequiresModifierPragma z = (RequiresModifierPragma)o;
      if (!(y.expressions == null && z.expressions == null)) {
         if (y.expressions != null && z.expressions != null && (z.expressions.size() == y.expressions.size())) {
            for (int i = 0; i < z.expressions.size(); i++) {
               x = x && ((Boolean)z.expressions.elementAt(i).accept(this, y.expressions.elementAt(i))).booleanValue();
            }
         } else {
            x = false;
         }
      }
      return new Boolean(x);
   }

   //@ ensures RES!=null
   public Object visitGuardedByModifierPragma(GuardedByModifierPragma y, Object o) {
      Boolean _tmp = (Boolean)prep(y,o);
      if (_tmp!=null) return _tmp;
      if (!(o instanceof GuardedByModifierPragma)) return new Boolean(false);
      boolean x = true;  
      GuardedByModifierPragma z = (GuardedByModifierPragma)o;
      if (!(y.expressions == null && z.expressions == null)) {
         if (y.expressions != null && z.expressions != null && (z.expressions.size() == y.expressions.size())) {
            for (int i = 0; i < z.expressions.size(); i++) {
               x = x && ((Boolean)z.expressions.elementAt(i).accept(this, y.expressions.elementAt(i))).booleanValue();
            }
         } else {
            x = false;
         }
      }
      return new Boolean(x);
   }

   //@ ensures RES!=null
   public Object visitThreadLocalStatusPragma(ThreadLocalStatusPragma y, Object o) {
      Boolean _tmp = (Boolean)prep(y,o);
      if (_tmp!=null) return _tmp;
      if (!(o instanceof ThreadLocalStatusPragma)) return new Boolean(false);
      boolean x = true;  
      ThreadLocalStatusPragma z = (ThreadLocalStatusPragma)o;
      return new Boolean(x);
   }

   //@ ensures RES!=null
   public Object visitArrayGuardModifierPragma(ArrayGuardModifierPragma y, Object o) {
      Boolean _tmp = (Boolean)prep(y,o);
      if (_tmp!=null) return _tmp;
      if (!(o instanceof ArrayGuardModifierPragma)) return new Boolean(false);
      boolean x = true;  
      ArrayGuardModifierPragma z = (ArrayGuardModifierPragma)o;
      if (!(y.expressions == null && z.expressions == null)) {
         if (y.expressions != null && z.expressions != null && (z.expressions.size() == y.expressions.size())) {
            for (int i = 0; i < z.expressions.size(); i++) {
               x = x && ((Boolean)z.expressions.elementAt(i).accept(this, y.expressions.elementAt(i))).booleanValue();
            }
         } else {
            x = false;
         }
      }
      return new Boolean(x);
   }

   //@ ensures RES!=null
   public Object visitNowarnPragma(NowarnPragma y, Object o) {
      Boolean _tmp = (Boolean)prep(y,o);
      if (_tmp!=null) return _tmp;
      if (!(o instanceof NowarnPragma)) return new Boolean(false);
      boolean x = true;  
      NowarnPragma z = (NowarnPragma)o;
      x = x && (z.checks == y.checks);
      return new Boolean(x);
   }

   //@ ensures RES!=null
   public Object visitGenericArgumentPragma(GenericArgumentPragma y, Object o) {
      Boolean _tmp = (Boolean)prep(y,o);
      if (_tmp!=null) return _tmp;
      if (!(o instanceof GenericArgumentPragma)) return new Boolean(false);
      boolean x = true;  
      GenericArgumentPragma z = (GenericArgumentPragma)o;
      if (!(y.expressions == null && z.expressions == null)) {
         if (y.expressions != null && z.expressions != null && (z.expressions.size() == y.expressions.size())) {
            for (int i = 0; i < z.expressions.size(); i++) {
               x = x && ((Boolean)z.expressions.elementAt(i).accept(this, y.expressions.elementAt(i))).booleanValue();
            }
         } else {
            x = false;
         }
      }
      return new Boolean(x);
   }

   //@ ensures RES!=null
   public Object visitGenericParameterPragma(GenericParameterPragma y, Object o) {
      Boolean _tmp = (Boolean)prep(y,o);
      if (_tmp!=null) return _tmp;
      if (!(o instanceof GenericParameterPragma)) return new Boolean(false);
      boolean x = true;  
      GenericParameterPragma z = (GenericParameterPragma)o;
      if (!(y.args == null && z.args == null)) {
         if (y.args != null && z.args != null && (z.args.size() == y.args.size())) {
            for (int i = 0; i < z.args.size(); i++) {
               x = x && ((Boolean)z.args.elementAt(i).accept(this, y.args.elementAt(i))).booleanValue();
            }
         } else {
            x = false;
         }
      }
      return new Boolean(x);
   }

   //@ ensures RES!=null
   public Object visitGhostDeclPragma(GhostDeclPragma y, Object o) {
      Boolean _tmp = (Boolean)prep(y,o);
      if (_tmp!=null) return _tmp;
      if (!(o instanceof GhostDeclPragma)) return new Boolean(false);
      boolean x = true;  
      GhostDeclPragma z = (GhostDeclPragma)o;
      x = x && (y.decl == null && z.decl == null ||  (y.decl != null && z.decl != null && ((Boolean)(y.decl.accept(this, z.decl))).booleanValue()));
      return new Boolean(x);
   }

  //@ requires x!=null
    public Object visitReadOnlyModifierPragma(ReadOnlyModifierPragma x, Object o) {
     Boolean _tmp = (Boolean)prep(x,o);
      if (_tmp!=null) return _tmp;
      if (!(o instanceof ReadOnlyModifierPragma)) return new Boolean(false);
      return new Boolean(true);
    }

}
