/* Copyright 2000, 2001, Compaq Computer Corporation */

package rcc.ast;

import javafe.ast.ASTNode;
import javafe.ast.AmbiguousMethodInvocation;
import javafe.ast.AmbiguousVariableAccess;
import javafe.ast.ArrayInit;
import javafe.ast.ArrayRefExpr;
import javafe.ast.ArrayType;
import javafe.ast.BinaryExpr;
import javafe.ast.BlockStmt;
import javafe.ast.BranchStmt;
import javafe.ast.BreakStmt;
import javafe.ast.CastExpr;
import javafe.ast.CatchClause;
import javafe.ast.CatchClauseVec;
import javafe.ast.ClassDecl;
import javafe.ast.ClassDeclStmt;
import javafe.ast.ClassLiteral;
import javafe.ast.CompilationUnit;
import javafe.ast.CompoundName;
import javafe.ast.CondExpr;
import javafe.ast.ConstructorDecl;
import javafe.ast.ConstructorInvocation;
import javafe.ast.ContinueStmt;
import javafe.ast.DoStmt;
import javafe.ast.EvalStmt;
import javafe.ast.Expr;
import javafe.ast.ExprObjectDesignator;
import javafe.ast.ExprVec;
import javafe.ast.FieldAccess;
import javafe.ast.FieldDecl;
import javafe.ast.ForStmt;
import javafe.ast.FormalParaDecl;
import javafe.ast.FormalParaDeclVec;
import javafe.ast.GenericBlockStmt;
import javafe.ast.GenericVarDecl;
import javafe.ast.IfStmt;
import javafe.ast.ImportDecl;
import javafe.ast.ImportDeclVec;
import javafe.ast.InitBlock;
import javafe.ast.InstanceOfExpr;
import javafe.ast.InterfaceDecl;
import javafe.ast.LabelStmt;
import javafe.ast.LexicalPragma;
import javafe.ast.LexicalPragmaVec;
import javafe.ast.LiteralExpr;
import javafe.ast.LocalVarDecl;
import javafe.ast.MethodDecl;
import javafe.ast.MethodInvocation;
import javafe.ast.ModifierPragma;
import javafe.ast.ModifierPragmaVec;
import javafe.ast.Name;
import javafe.ast.NewArrayExpr;
import javafe.ast.NewInstanceExpr;
import javafe.ast.ObjectDesignator;
import javafe.ast.OnDemandImportDecl;
import javafe.ast.ParenExpr;
import javafe.ast.PrimitiveType;
import javafe.ast.ReturnStmt;
import javafe.ast.RoutineDecl;
import javafe.ast.SimpleName;
import javafe.ast.SingleTypeImportDecl;
import javafe.ast.SkipStmt;
import javafe.ast.Stmt;
import javafe.ast.StmtPragma;
import javafe.ast.StmtVec;
import javafe.ast.SuperObjectDesignator;
import javafe.ast.SwitchLabel;
import javafe.ast.SwitchStmt;
import javafe.ast.SynchronizeStmt;
import javafe.ast.ThisExpr;
import javafe.ast.ThrowStmt;
import javafe.ast.TryCatchStmt;
import javafe.ast.TryFinallyStmt;
import javafe.ast.Type;
import javafe.ast.TypeDecl;
import javafe.ast.TypeDeclElem;
import javafe.ast.TypeDeclElemPragma;
import javafe.ast.TypeDeclElemVec;
import javafe.ast.TypeDeclVec;
import javafe.ast.TypeModifierPragma;
import javafe.ast.TypeModifierPragmaVec;
import javafe.ast.TypeName;
import javafe.ast.TypeNameVec;
import javafe.ast.TypeObjectDesignator;
import javafe.ast.UnaryExpr;
import javafe.ast.VarDeclStmt;
import javafe.ast.VarInit;
import javafe.ast.VarInitVec;
import javafe.ast.VariableAccess;
import javafe.ast.WhileStmt;

// Convention: unless otherwise noted, integer fields named "loc" refer
// to the location of the first character of the syntactic unit

public class CloneVisitorSuper extends rcc.ast.VisitorArgResult {
    public ASTNode prep(ASTNode y, Object o) {
        return null;
    }

    public ASTNode finish(ASTNode y, Object o) {
        return y;
    }

    // @ ensures RES!=null
    public Object visitASTNode(ASTNode y, Object o) {
        return finish((ASTNode) y.clone(), o);
    }

    // @ ensures RES!=null
    public Object visitCompilationUnit(CompilationUnit y, Object o) {
        {
            ASTNode a = prep(y, o);
            if (a != null) return a;
        }
        CompilationUnit x = (CompilationUnit) y.clone();
        Name _temppkgName = (Name) (x.pkgName == null ? null
            : x.pkgName.accept(this, o));
        x.pkgName = _temppkgName;
        LexicalPragmaVec _templexicalPragmas;
        if (x.lexicalPragmas == null) {
            _templexicalPragmas = null;
        } else {
            _templexicalPragmas = LexicalPragmaVec.make(x.lexicalPragmas.size());

            for (int i = 0; i < x.lexicalPragmas.size(); i++) {
                _templexicalPragmas.insertElementAt(
                    (LexicalPragma) x.lexicalPragmas.elementAt(i).accept(
                        this,
                        o),
                    i);
            }
        }
        x.lexicalPragmas = _templexicalPragmas;
        ImportDeclVec _tempimports;
        if (x.imports == null) {
            _tempimports = null;
        } else {
            _tempimports = ImportDeclVec.make(x.imports.size());

            for (int i = 0; i < x.imports.size(); i++) {
                _tempimports.insertElementAt(
                    (ImportDecl) x.imports.elementAt(i).accept(this, o),
                    i);
            }
        }
        x.imports = _tempimports;
        TypeDeclVec _tempelems;
        if (x.elems == null) {
            _tempelems = null;
        } else {
            _tempelems = TypeDeclVec.make(x.elems.size());

            for (int i = 0; i < x.elems.size(); i++) {
                _tempelems.insertElementAt(
                    (TypeDecl) x.elems.elementAt(i).accept(this, o),
                    i);
            }
        }
        x.elems = _tempelems;
        return finish(x, o);
    }

    // @ ensures RES!=null
    public Object visitImportDecl(ImportDecl y, Object o) {
        return visitASTNode(y, o);
    }

    // @ ensures RES!=null
    public Object visitSingleTypeImportDecl(SingleTypeImportDecl y, Object o) {
        {
            ASTNode a = prep(y, o);
            if (a != null) return a;
        }
        SingleTypeImportDecl x = (SingleTypeImportDecl) y.clone();
        TypeName _temptypeName = (TypeName) (x.typeName == null ? null
            : x.typeName.accept(this, o));
        x.typeName = _temptypeName;
        return finish(x, o);
    }

    // @ ensures RES!=null
    public Object visitOnDemandImportDecl(OnDemandImportDecl y, Object o) {
        {
            ASTNode a = prep(y, o);
            if (a != null) return a;
        }
        OnDemandImportDecl x = (OnDemandImportDecl) y.clone();
        Name _temppkgName = (Name) (x.pkgName == null ? null
            : x.pkgName.accept(this, o));
        x.pkgName = _temppkgName;
        return finish(x, o);
    }

    // @ ensures RES!=null
    public Object visitTypeDecl(TypeDecl y, Object o) {
        return visitASTNode(y, o);
    }

    // @ ensures RES!=null
    public Object visitClassDecl(ClassDecl y, Object o) {
        {
            ASTNode a = prep(y, o);
            if (a != null) return a;
        }
        ClassDecl x = (ClassDecl) y.clone();
        ModifierPragmaVec _temppmodifiers;
        if (x.pmodifiers == null) {
            _temppmodifiers = null;
        } else {
            _temppmodifiers = ModifierPragmaVec.make(x.pmodifiers.size());

            for (int i = 0; i < x.pmodifiers.size(); i++) {
                _temppmodifiers.insertElementAt(
                    (ModifierPragma) x.pmodifiers.elementAt(i).accept(this, o),
                    i);
            }
        }
        x.pmodifiers = _temppmodifiers;
        TypeModifierPragmaVec _temptmodifiers;
        if (x.tmodifiers == null) {
            _temptmodifiers = null;
        } else {
            _temptmodifiers = TypeModifierPragmaVec.make(x.tmodifiers.size());

            for (int i = 0; i < x.tmodifiers.size(); i++) {
                _temptmodifiers.insertElementAt(
                    (TypeModifierPragma) x.tmodifiers.elementAt(i).accept(
                        this,
                        o),
                    i);
            }
        }
        x.tmodifiers = _temptmodifiers;
        TypeNameVec _tempsuperInterfaces;
        if (x.superInterfaces == null) {
            _tempsuperInterfaces = null;
        } else {
            _tempsuperInterfaces = TypeNameVec.make(x.superInterfaces.size());

            for (int i = 0; i < x.superInterfaces.size(); i++) {
                _tempsuperInterfaces.insertElementAt(
                    (TypeName) x.superInterfaces.elementAt(i).accept(this, o),
                    i);
            }
        }
        x.superInterfaces = _tempsuperInterfaces;
        TypeDeclElemVec _tempelems;
        if (x.elems == null) {
            _tempelems = null;
        } else {
            _tempelems = TypeDeclElemVec.make(x.elems.size());

            for (int i = 0; i < x.elems.size(); i++) {
                _tempelems.insertElementAt(
                    (TypeDeclElem) x.elems.elementAt(i).accept(this, o),
                    i);
            }
        }
        x.elems = _tempelems;
        TypeName _tempsuperClass = (TypeName) (x.superClass == null ? null
            : x.superClass.accept(this, o));
        x.superClass = _tempsuperClass;
        return finish(x, o);
    }

    // @ ensures RES!=null
    public Object visitInterfaceDecl(InterfaceDecl y, Object o) {
        {
            ASTNode a = prep(y, o);
            if (a != null) return a;
        }
        InterfaceDecl x = (InterfaceDecl) y.clone();
        ModifierPragmaVec _temppmodifiers;
        if (x.pmodifiers == null) {
            _temppmodifiers = null;
        } else {
            _temppmodifiers = ModifierPragmaVec.make(x.pmodifiers.size());

            for (int i = 0; i < x.pmodifiers.size(); i++) {
                _temppmodifiers.insertElementAt(
                    (ModifierPragma) x.pmodifiers.elementAt(i).accept(this, o),
                    i);
            }
        }
        x.pmodifiers = _temppmodifiers;
        TypeModifierPragmaVec _temptmodifiers;
        if (x.tmodifiers == null) {
            _temptmodifiers = null;
        } else {
            _temptmodifiers = TypeModifierPragmaVec.make(x.tmodifiers.size());

            for (int i = 0; i < x.tmodifiers.size(); i++) {
                _temptmodifiers.insertElementAt(
                    (TypeModifierPragma) x.tmodifiers.elementAt(i).accept(
                        this,
                        o),
                    i);
            }
        }
        x.tmodifiers = _temptmodifiers;
        TypeNameVec _tempsuperInterfaces;
        if (x.superInterfaces == null) {
            _tempsuperInterfaces = null;
        } else {
            _tempsuperInterfaces = TypeNameVec.make(x.superInterfaces.size());

            for (int i = 0; i < x.superInterfaces.size(); i++) {
                _tempsuperInterfaces.insertElementAt(
                    (TypeName) x.superInterfaces.elementAt(i).accept(this, o),
                    i);
            }
        }
        x.superInterfaces = _tempsuperInterfaces;
        TypeDeclElemVec _tempelems;
        if (x.elems == null) {
            _tempelems = null;
        } else {
            _tempelems = TypeDeclElemVec.make(x.elems.size());

            for (int i = 0; i < x.elems.size(); i++) {
                _tempelems.insertElementAt(
                    (TypeDeclElem) x.elems.elementAt(i).accept(this, o),
                    i);
            }
        }
        x.elems = _tempelems;
        return finish(x, o);
    }

    // @ ensures RES!=null
    public Object visitRoutineDecl(RoutineDecl y, Object o) {
        return visitASTNode(y, o);
    }

    // @ ensures RES!=null
    public Object visitConstructorDecl(ConstructorDecl y, Object o) {
        {
            ASTNode a = prep(y, o);
            if (a != null) return a;
        }
        ConstructorDecl x = (ConstructorDecl) y.clone();
        ModifierPragmaVec _temppmodifiers;
        if (x.pmodifiers == null) {
            _temppmodifiers = null;
        } else {
            _temppmodifiers = ModifierPragmaVec.make(x.pmodifiers.size());

            for (int i = 0; i < x.pmodifiers.size(); i++) {
                _temppmodifiers.insertElementAt(
                    (ModifierPragma) x.pmodifiers.elementAt(i).accept(this, o),
                    i);
            }
        }
        x.pmodifiers = _temppmodifiers;
        TypeModifierPragmaVec _temptmodifiers;
        if (x.tmodifiers == null) {
            _temptmodifiers = null;
        } else {
            _temptmodifiers = TypeModifierPragmaVec.make(x.tmodifiers.size());

            for (int i = 0; i < x.tmodifiers.size(); i++) {
                _temptmodifiers.insertElementAt(
                    (TypeModifierPragma) x.tmodifiers.elementAt(i).accept(
                        this,
                        o),
                    i);
            }
        }
        x.tmodifiers = _temptmodifiers;
        FormalParaDeclVec _tempargs;
        if (x.args == null) {
            _tempargs = null;
        } else {
            _tempargs = FormalParaDeclVec.make(x.args.size());

            for (int i = 0; i < x.args.size(); i++) {
                _tempargs.insertElementAt(
                    (FormalParaDecl) x.args.elementAt(i).accept(this, o),
                    i);
            }
        }
        x.args = _tempargs;
        TypeNameVec _tempraises;
        if (x.raises == null) {
            _tempraises = null;
        } else {
            _tempraises = TypeNameVec.make(x.raises.size());

            for (int i = 0; i < x.raises.size(); i++) {
                _tempraises.insertElementAt(
                    (TypeName) x.raises.elementAt(i).accept(this, o),
                    i);
            }
        }
        x.raises = _tempraises;
        BlockStmt _tempbody = (BlockStmt) (x.body == null ? null
            : x.body.accept(this, o));
        x.body = _tempbody;
        return finish(x, o);
    }

    // @ ensures RES!=null
    public Object visitMethodDecl(MethodDecl y, Object o) {
        {
            ASTNode a = prep(y, o);
            if (a != null) return a;
        }
        MethodDecl x = (MethodDecl) y.clone();
        ModifierPragmaVec _temppmodifiers;
        if (x.pmodifiers == null) {
            _temppmodifiers = null;
        } else {
            _temppmodifiers = ModifierPragmaVec.make(x.pmodifiers.size());

            for (int i = 0; i < x.pmodifiers.size(); i++) {
                _temppmodifiers.insertElementAt(
                    (ModifierPragma) x.pmodifiers.elementAt(i).accept(this, o),
                    i);
            }
        }
        x.pmodifiers = _temppmodifiers;
        TypeModifierPragmaVec _temptmodifiers;
        if (x.tmodifiers == null) {
            _temptmodifiers = null;
        } else {
            _temptmodifiers = TypeModifierPragmaVec.make(x.tmodifiers.size());

            for (int i = 0; i < x.tmodifiers.size(); i++) {
                _temptmodifiers.insertElementAt(
                    (TypeModifierPragma) x.tmodifiers.elementAt(i).accept(
                        this,
                        o),
                    i);
            }
        }
        x.tmodifiers = _temptmodifiers;
        FormalParaDeclVec _tempargs;
        if (x.args == null) {
            _tempargs = null;
        } else {
            _tempargs = FormalParaDeclVec.make(x.args.size());

            for (int i = 0; i < x.args.size(); i++) {
                _tempargs.insertElementAt(
                    (FormalParaDecl) x.args.elementAt(i).accept(this, o),
                    i);
            }
        }
        x.args = _tempargs;
        TypeNameVec _tempraises;
        if (x.raises == null) {
            _tempraises = null;
        } else {
            _tempraises = TypeNameVec.make(x.raises.size());

            for (int i = 0; i < x.raises.size(); i++) {
                _tempraises.insertElementAt(
                    (TypeName) x.raises.elementAt(i).accept(this, o),
                    i);
            }
        }
        x.raises = _tempraises;
        BlockStmt _tempbody = (BlockStmt) (x.body == null ? null
            : x.body.accept(this, o));
        x.body = _tempbody;
        Type _tempreturnType = (Type) (x.returnType == null ? null
            : x.returnType.accept(this, o));
        x.returnType = _tempreturnType;
        return finish(x, o);
    }

    // @ ensures RES!=null
    public Object visitInitBlock(InitBlock y, Object o) {
        {
            ASTNode a = prep(y, o);
            if (a != null) return a;
        }
        InitBlock x = (InitBlock) y.clone();
        ModifierPragmaVec _temppmodifiers;
        if (x.pmodifiers == null) {
            _temppmodifiers = null;
        } else {
            _temppmodifiers = ModifierPragmaVec.make(x.pmodifiers.size());

            for (int i = 0; i < x.pmodifiers.size(); i++) {
                _temppmodifiers.insertElementAt(
                    (ModifierPragma) x.pmodifiers.elementAt(i).accept(this, o),
                    i);
            }
        }
        x.pmodifiers = _temppmodifiers;
        BlockStmt _tempblock = (BlockStmt) (x.block == null ? null
            : x.block.accept(this, o));
        x.block = _tempblock;
        return finish(x, o);
    }

    // @ ensures RES!=null
    public Object visitTypeDeclElemPragma(TypeDeclElemPragma y, Object o) {
        return visitASTNode(y, o);
    }

    // @ ensures RES!=null
    public Object visitGenericVarDecl(GenericVarDecl y, Object o) {
        return visitASTNode(y, o);
    }

    // @ ensures RES!=null
    public Object visitLocalVarDecl(LocalVarDecl y, Object o) {
        {
            ASTNode a = prep(y, o);
            if (a != null) return a;
        }
        LocalVarDecl x = (LocalVarDecl) y.clone();
        ModifierPragmaVec _temppmodifiers;
        if (x.pmodifiers == null) {
            _temppmodifiers = null;
        } else {
            _temppmodifiers = ModifierPragmaVec.make(x.pmodifiers.size());

            for (int i = 0; i < x.pmodifiers.size(); i++) {
                _temppmodifiers.insertElementAt(
                    (ModifierPragma) x.pmodifiers.elementAt(i).accept(this, o),
                    i);
            }
        }
        x.pmodifiers = _temppmodifiers;
        Type _temptype = (Type) (x.type == null ? null : x.type.accept(this, o));
        x.type = _temptype;
        VarInit _tempinit = (VarInit) (x.init == null ? null : x.init.accept(
            this,
            o));
        x.init = _tempinit;
        return finish(x, o);
    }

    // @ ensures RES!=null
    public Object visitFieldDecl(FieldDecl y, Object o) {
        {
            ASTNode a = prep(y, o);
            if (a != null) return a;
        }
        FieldDecl x = (FieldDecl) y.clone();
        ModifierPragmaVec _temppmodifiers;
        if (x.pmodifiers == null) {
            _temppmodifiers = null;
        } else {
            _temppmodifiers = ModifierPragmaVec.make(x.pmodifiers.size());

            for (int i = 0; i < x.pmodifiers.size(); i++) {
                _temppmodifiers.insertElementAt(
                    (ModifierPragma) x.pmodifiers.elementAt(i).accept(this, o),
                    i);
            }
        }
        x.pmodifiers = _temppmodifiers;
        Type _temptype = (Type) (x.type == null ? null : x.type.accept(this, o));
        x.type = _temptype;
        VarInit _tempinit = (VarInit) (x.init == null ? null : x.init.accept(
            this,
            o));
        x.init = _tempinit;
        return finish(x, o);
    }

    // @ ensures RES!=null
    public Object visitFormalParaDecl(FormalParaDecl y, Object o) {
        {
            ASTNode a = prep(y, o);
            if (a != null) return a;
        }
        FormalParaDecl x = (FormalParaDecl) y.clone();
        ModifierPragmaVec _temppmodifiers;
        if (x.pmodifiers == null) {
            _temppmodifiers = null;
        } else {
            _temppmodifiers = ModifierPragmaVec.make(x.pmodifiers.size());

            for (int i = 0; i < x.pmodifiers.size(); i++) {
                _temppmodifiers.insertElementAt(
                    (ModifierPragma) x.pmodifiers.elementAt(i).accept(this, o),
                    i);
            }
        }
        x.pmodifiers = _temppmodifiers;
        Type _temptype = (Type) (x.type == null ? null : x.type.accept(this, o));
        x.type = _temptype;
        return finish(x, o);
    }

    // @ ensures RES!=null
    public Object visitStmt(Stmt y, Object o) {
        return visitASTNode(y, o);
    }

    // @ ensures RES!=null
    public Object visitGenericBlockStmt(GenericBlockStmt y, Object o) {
        return visitStmt(y, o);
    }

    // @ ensures RES!=null
    public Object visitBlockStmt(BlockStmt y, Object o) {
        {
            ASTNode a = prep(y, o);
            if (a != null) return a;
        }
        BlockStmt x = (BlockStmt) y.clone();
        StmtVec _tempstmts;
        if (x.stmts == null) {
            _tempstmts = null;
        } else {
            _tempstmts = StmtVec.make(x.stmts.size());

            for (int i = 0; i < x.stmts.size(); i++) {
                _tempstmts.insertElementAt((Stmt) x.stmts.elementAt(i).accept(
                    this,
                    o), i);
            }
        }
        x.stmts = _tempstmts;
        return finish(x, o);
    }

    // @ ensures RES!=null
    public Object visitSwitchStmt(SwitchStmt y, Object o) {
        {
            ASTNode a = prep(y, o);
            if (a != null) return a;
        }
        SwitchStmt x = (SwitchStmt) y.clone();
        StmtVec _tempstmts;
        if (x.stmts == null) {
            _tempstmts = null;
        } else {
            _tempstmts = StmtVec.make(x.stmts.size());

            for (int i = 0; i < x.stmts.size(); i++) {
                _tempstmts.insertElementAt((Stmt) x.stmts.elementAt(i).accept(
                    this,
                    o), i);
            }
        }
        x.stmts = _tempstmts;
        Expr _tempexpr = (Expr) (x.expr == null ? null : x.expr.accept(this, o));
        x.expr = _tempexpr;
        return finish(x, o);
    }

    // @ ensures RES!=null
    public Object visitVarDeclStmt(VarDeclStmt y, Object o) {
        {
            ASTNode a = prep(y, o);
            if (a != null) return a;
        }
        VarDeclStmt x = (VarDeclStmt) y.clone();
        LocalVarDecl _tempdecl = (LocalVarDecl) (x.decl == null ? null
            : x.decl.accept(this, o));
        x.decl = _tempdecl;
        return finish(x, o);
    }

    // @ ensures RES!=null
    public Object visitClassDeclStmt(ClassDeclStmt y, Object o) {
        {
            ASTNode a = prep(y, o);
            if (a != null) return a;
        }
        ClassDeclStmt x = (ClassDeclStmt) y.clone();
        ClassDecl _tempdecl = (ClassDecl) (x.decl == null ? null
            : x.decl.accept(this, o));
        x.decl = _tempdecl;
        return finish(x, o);
    }

    // @ ensures RES!=null
    public Object visitWhileStmt(WhileStmt y, Object o) {
        {
            ASTNode a = prep(y, o);
            if (a != null) return a;
        }
        WhileStmt x = (WhileStmt) y.clone();
        Expr _tempexpr = (Expr) (x.expr == null ? null : x.expr.accept(this, o));
        x.expr = _tempexpr;
        Stmt _tempstmt = (Stmt) (x.stmt == null ? null : x.stmt.accept(this, o));
        x.stmt = _tempstmt;
        return finish(x, o);
    }

    // @ ensures RES!=null
    public Object visitDoStmt(DoStmt y, Object o) {
        {
            ASTNode a = prep(y, o);
            if (a != null) return a;
        }
        DoStmt x = (DoStmt) y.clone();
        Expr _tempexpr = (Expr) (x.expr == null ? null : x.expr.accept(this, o));
        x.expr = _tempexpr;
        Stmt _tempstmt = (Stmt) (x.stmt == null ? null : x.stmt.accept(this, o));
        x.stmt = _tempstmt;
        return finish(x, o);
    }

    // @ ensures RES!=null
    public Object visitSynchronizeStmt(SynchronizeStmt y, Object o) {
        {
            ASTNode a = prep(y, o);
            if (a != null) return a;
        }
        SynchronizeStmt x = (SynchronizeStmt) y.clone();
        Expr _tempexpr = (Expr) (x.expr == null ? null : x.expr.accept(this, o));
        x.expr = _tempexpr;
        BlockStmt _tempstmt = (BlockStmt) (x.stmt == null ? null
            : x.stmt.accept(this, o));
        x.stmt = _tempstmt;
        return finish(x, o);
    }

    // @ ensures RES!=null
    public Object visitEvalStmt(EvalStmt y, Object o) {
        {
            ASTNode a = prep(y, o);
            if (a != null) return a;
        }
        EvalStmt x = (EvalStmt) y.clone();
        Expr _tempexpr = (Expr) (x.expr == null ? null : x.expr.accept(this, o));
        x.expr = _tempexpr;
        return finish(x, o);
    }

    // @ ensures RES!=null
    public Object visitReturnStmt(ReturnStmt y, Object o) {
        {
            ASTNode a = prep(y, o);
            if (a != null) return a;
        }
        ReturnStmt x = (ReturnStmt) y.clone();
        Expr _tempexpr = (Expr) (x.expr == null ? null : x.expr.accept(this, o));
        x.expr = _tempexpr;
        return finish(x, o);
    }

    // @ ensures RES!=null
    public Object visitThrowStmt(ThrowStmt y, Object o) {
        {
            ASTNode a = prep(y, o);
            if (a != null) return a;
        }
        ThrowStmt x = (ThrowStmt) y.clone();
        Expr _tempexpr = (Expr) (x.expr == null ? null : x.expr.accept(this, o));
        x.expr = _tempexpr;
        return finish(x, o);
    }

    // @ ensures RES!=null
    public Object visitBranchStmt(BranchStmt y, Object o) {
        return visitStmt(y, o);
    }

    // @ ensures RES!=null
    public Object visitBreakStmt(BreakStmt y, Object o) {
        {
            ASTNode a = prep(y, o);
            if (a != null) return a;
        }
        BreakStmt x = (BreakStmt) y.clone();
        return finish(x, o);
    }

    // @ ensures RES!=null
    public Object visitContinueStmt(ContinueStmt y, Object o) {
        {
            ASTNode a = prep(y, o);
            if (a != null) return a;
        }
        ContinueStmt x = (ContinueStmt) y.clone();
        return finish(x, o);
    }

    // @ ensures RES!=null
    public Object visitLabelStmt(LabelStmt y, Object o) {
        {
            ASTNode a = prep(y, o);
            if (a != null) return a;
        }
        LabelStmt x = (LabelStmt) y.clone();
        Stmt _tempstmt = (Stmt) (x.stmt == null ? null : x.stmt.accept(this, o));
        x.stmt = _tempstmt;
        return finish(x, o);
    }

    // @ ensures RES!=null
    public Object visitIfStmt(IfStmt y, Object o) {
        {
            ASTNode a = prep(y, o);
            if (a != null) return a;
        }
        IfStmt x = (IfStmt) y.clone();
        Expr _tempexpr = (Expr) (x.expr == null ? null : x.expr.accept(this, o));
        x.expr = _tempexpr;
        Stmt _tempthn = (Stmt) (x.thn == null ? null : x.thn.accept(this, o));
        x.thn = _tempthn;
        Stmt _tempels = (Stmt) (x.els == null ? null : x.els.accept(this, o));
        x.els = _tempels;
        return finish(x, o);
    }

    // @ ensures RES!=null
    public Object visitForStmt(ForStmt y, Object o) {
        {
            ASTNode a = prep(y, o);
            if (a != null) return a;
        }
        ForStmt x = (ForStmt) y.clone();
        StmtVec _tempforInit;
        if (x.forInit == null) {
            _tempforInit = null;
        } else {
            _tempforInit = StmtVec.make(x.forInit.size());

            for (int i = 0; i < x.forInit.size(); i++) {
                _tempforInit.insertElementAt(
                    (Stmt) x.forInit.elementAt(i).accept(this, o),
                    i);
            }
        }
        x.forInit = _tempforInit;
        Expr _temptest = (Expr) (x.test == null ? null : x.test.accept(this, o));
        x.test = _temptest;
        ExprVec _tempforUpdate;
        if (x.forUpdate == null) {
            _tempforUpdate = null;
        } else {
            _tempforUpdate = ExprVec.make(x.forUpdate.size());

            for (int i = 0; i < x.forUpdate.size(); i++) {
                _tempforUpdate.insertElementAt(
                    (Expr) x.forUpdate.elementAt(i).accept(this, o),
                    i);
            }
        }
        x.forUpdate = _tempforUpdate;
        Stmt _tempbody = (Stmt) (x.body == null ? null : x.body.accept(this, o));
        x.body = _tempbody;
        return finish(x, o);
    }

    // @ ensures RES!=null
    public Object visitSkipStmt(SkipStmt y, Object o) {
        {
            ASTNode a = prep(y, o);
            if (a != null) return a;
        }
        SkipStmt x = (SkipStmt) y.clone();
        return finish(x, o);
    }

    // @ ensures RES!=null
    public Object visitSwitchLabel(SwitchLabel y, Object o) {
        {
            ASTNode a = prep(y, o);
            if (a != null) return a;
        }
        SwitchLabel x = (SwitchLabel) y.clone();
        Expr _tempexpr = (Expr) (x.expr == null ? null : x.expr.accept(this, o));
        x.expr = _tempexpr;
        return finish(x, o);
    }

    // @ ensures RES!=null
    public Object visitTryFinallyStmt(TryFinallyStmt y, Object o) {
        {
            ASTNode a = prep(y, o);
            if (a != null) return a;
        }
        TryFinallyStmt x = (TryFinallyStmt) y.clone();
        Stmt _temptryClause = (Stmt) (x.tryClause == null ? null
            : x.tryClause.accept(this, o));
        x.tryClause = _temptryClause;
        Stmt _tempfinallyClause = (Stmt) (x.finallyClause == null ? null
            : x.finallyClause.accept(this, o));
        x.finallyClause = _tempfinallyClause;
        return finish(x, o);
    }

    // @ ensures RES!=null
    public Object visitTryCatchStmt(TryCatchStmt y, Object o) {
        {
            ASTNode a = prep(y, o);
            if (a != null) return a;
        }
        TryCatchStmt x = (TryCatchStmt) y.clone();
        Stmt _temptryClause = (Stmt) (x.tryClause == null ? null
            : x.tryClause.accept(this, o));
        x.tryClause = _temptryClause;
        CatchClauseVec _tempcatchClauses;
        if (x.catchClauses == null) {
            _tempcatchClauses = null;
        } else {
            _tempcatchClauses = CatchClauseVec.make(x.catchClauses.size());

            for (int i = 0; i < x.catchClauses.size(); i++) {
                _tempcatchClauses.insertElementAt(
                    (CatchClause) x.catchClauses.elementAt(i).accept(this, o),
                    i);
            }
        }
        x.catchClauses = _tempcatchClauses;
        return finish(x, o);
    }

    // @ ensures RES!=null
    public Object visitStmtPragma(StmtPragma y, Object o) {
        return visitStmt(y, o);
    }

    // @ ensures RES!=null
    public Object visitConstructorInvocation(ConstructorInvocation y, Object o) {
        {
            ASTNode a = prep(y, o);
            if (a != null) return a;
        }
        ConstructorInvocation x = (ConstructorInvocation) y.clone();
        Expr _tempenclosingInstance = (Expr) (x.enclosingInstance == null ? null
            : x.enclosingInstance.accept(this, o));
        x.enclosingInstance = _tempenclosingInstance;
        ExprVec _tempargs;
        if (x.args == null) {
            _tempargs = null;
        } else {
            _tempargs = ExprVec.make(x.args.size());

            for (int i = 0; i < x.args.size(); i++) {
                _tempargs.insertElementAt((Expr) x.args.elementAt(i).accept(
                    this,
                    o), i);
            }
        }
        x.args = _tempargs;
        return finish(x, o);
    }

    // @ ensures RES!=null
    public Object visitCatchClause(CatchClause y, Object o) {
        {
            ASTNode a = prep(y, o);
            if (a != null) return a;
        }
        CatchClause x = (CatchClause) y.clone();
        FormalParaDecl _temparg = (FormalParaDecl) (x.arg == null ? null
            : x.arg.accept(this, o));
        x.arg = _temparg;
        BlockStmt _tempbody = (BlockStmt) (x.body == null ? null
            : x.body.accept(this, o));
        x.body = _tempbody;
        return finish(x, o);
    }

    // @ ensures RES!=null
    public Object visitVarInit(VarInit y, Object o) {
        return visitASTNode(y, o);
    }

    // @ ensures RES!=null
    public Object visitArrayInit(ArrayInit y, Object o) {
        {
            ASTNode a = prep(y, o);
            if (a != null) return a;
        }
        ArrayInit x = (ArrayInit) y.clone();
        VarInitVec _tempelems;
        if (x.elems == null) {
            _tempelems = null;
        } else {
            _tempelems = VarInitVec.make(x.elems.size());

            for (int i = 0; i < x.elems.size(); i++) {
                _tempelems.insertElementAt(
                    (VarInit) x.elems.elementAt(i).accept(this, o),
                    i);
            }
        }
        x.elems = _tempelems;
        return finish(x, o);
    }

    // @ ensures RES!=null
    public Object visitExpr(Expr y, Object o) {
        return visitVarInit(y, o);
    }

    // @ ensures RES!=null
    public Object visitThisExpr(ThisExpr y, Object o) {
        {
            ASTNode a = prep(y, o);
            if (a != null) return a;
        }
        ThisExpr x = (ThisExpr) y.clone();
        Type _tempclassPrefix = (Type) (x.classPrefix == null ? null
            : x.classPrefix.accept(this, o));
        x.classPrefix = _tempclassPrefix;
        return finish(x, o);
    }

    // @ ensures RES!=null
    public Object visitLiteralExpr(LiteralExpr y, Object o) {
        {
            ASTNode a = prep(y, o);
            if (a != null) return a;
        }
        LiteralExpr x = (LiteralExpr) y.clone();
        Object _tempvalue = x.value;
        x.value = _tempvalue;
        return finish(x, o);
    }

    // @ ensures RES!=null
    public Object visitArrayRefExpr(ArrayRefExpr y, Object o) {
        {
            ASTNode a = prep(y, o);
            if (a != null) return a;
        }
        ArrayRefExpr x = (ArrayRefExpr) y.clone();
        Expr _temparray = (Expr) (x.array == null ? null : x.array.accept(
            this,
            o));
        x.array = _temparray;
        Expr _tempindex = (Expr) (x.index == null ? null : x.index.accept(
            this,
            o));
        x.index = _tempindex;
        return finish(x, o);
    }

    // @ ensures RES!=null
    public Object visitNewInstanceExpr(NewInstanceExpr y, Object o) {
        {
            ASTNode a = prep(y, o);
            if (a != null) return a;
        }
        NewInstanceExpr x = (NewInstanceExpr) y.clone();
        Expr _tempenclosingInstance = (Expr) (x.enclosingInstance == null ? null
            : x.enclosingInstance.accept(this, o));
        x.enclosingInstance = _tempenclosingInstance;
        TypeName _temptype = (TypeName) (x.type == null ? null : x.type.accept(
            this,
            o));
        x.type = _temptype;
        ExprVec _tempargs;
        if (x.args == null) {
            _tempargs = null;
        } else {
            _tempargs = ExprVec.make(x.args.size());

            for (int i = 0; i < x.args.size(); i++) {
                _tempargs.insertElementAt((Expr) x.args.elementAt(i).accept(
                    this,
                    o), i);
            }
        }
        x.args = _tempargs;
        ClassDecl _tempanonDecl = (ClassDecl) (x.anonDecl == null ? null
            : x.anonDecl.accept(this, o));
        x.anonDecl = _tempanonDecl;
        return finish(x, o);
    }

    // @ ensures RES!=null
    public Object visitNewArrayExpr(NewArrayExpr y, Object o) {
        {
            ASTNode a = prep(y, o);
            if (a != null) return a;
        }
        NewArrayExpr x = (NewArrayExpr) y.clone();
        Type _temptype = (Type) (x.type == null ? null : x.type.accept(this, o));
        x.type = _temptype;
        ExprVec _tempdims;
        if (x.dims == null) {
            _tempdims = null;
        } else {
            _tempdims = ExprVec.make(x.dims.size());

            for (int i = 0; i < x.dims.size(); i++) {
                _tempdims.insertElementAt((Expr) x.dims.elementAt(i).accept(
                    this,
                    o), i);
            }
        }
        x.dims = _tempdims;
        ArrayInit _tempinit = (ArrayInit) (x.init == null ? null
            : x.init.accept(this, o));
        x.init = _tempinit;
        int[] _templocOpenBrackets = x.locOpenBrackets;
        x.locOpenBrackets = _templocOpenBrackets;
        return finish(x, o);
    }

    // @ ensures RES!=null
    public Object visitCondExpr(CondExpr y, Object o) {
        {
            ASTNode a = prep(y, o);
            if (a != null) return a;
        }
        CondExpr x = (CondExpr) y.clone();
        Expr _temptest = (Expr) (x.test == null ? null : x.test.accept(this, o));
        x.test = _temptest;
        Expr _tempthn = (Expr) (x.thn == null ? null : x.thn.accept(this, o));
        x.thn = _tempthn;
        Expr _tempels = (Expr) (x.els == null ? null : x.els.accept(this, o));
        x.els = _tempels;
        return finish(x, o);
    }

    // @ ensures RES!=null
    public Object visitInstanceOfExpr(InstanceOfExpr y, Object o) {
        {
            ASTNode a = prep(y, o);
            if (a != null) return a;
        }
        InstanceOfExpr x = (InstanceOfExpr) y.clone();
        Expr _tempexpr = (Expr) (x.expr == null ? null : x.expr.accept(this, o));
        x.expr = _tempexpr;
        Type _temptype = (Type) (x.type == null ? null : x.type.accept(this, o));
        x.type = _temptype;
        return finish(x, o);
    }

    // @ ensures RES!=null
    public Object visitCastExpr(CastExpr y, Object o) {
        {
            ASTNode a = prep(y, o);
            if (a != null) return a;
        }
        CastExpr x = (CastExpr) y.clone();
        Expr _tempexpr = (Expr) (x.expr == null ? null : x.expr.accept(this, o));
        x.expr = _tempexpr;
        Type _temptype = (Type) (x.type == null ? null : x.type.accept(this, o));
        x.type = _temptype;
        return finish(x, o);
    }

    // @ ensures RES!=null
    public Object visitBinaryExpr(BinaryExpr y, Object o) {
        {
            ASTNode a = prep(y, o);
            if (a != null) return a;
        }
        BinaryExpr x = (BinaryExpr) y.clone();
        Expr _templeft = (Expr) (x.left == null ? null : x.left.accept(this, o));
        x.left = _templeft;
        Expr _tempright = (Expr) (x.right == null ? null : x.right.accept(
            this,
            o));
        x.right = _tempright;
        return finish(x, o);
    }

    // @ ensures RES!=null
    public Object visitUnaryExpr(UnaryExpr y, Object o) {
        {
            ASTNode a = prep(y, o);
            if (a != null) return a;
        }
        UnaryExpr x = (UnaryExpr) y.clone();
        Expr _tempexpr = (Expr) (x.expr == null ? null : x.expr.accept(this, o));
        x.expr = _tempexpr;
        return finish(x, o);
    }

    // @ ensures RES!=null
    public Object visitParenExpr(ParenExpr y, Object o) {
        {
            ASTNode a = prep(y, o);
            if (a != null) return a;
        }
        ParenExpr x = (ParenExpr) y.clone();
        Expr _tempexpr = (Expr) (x.expr == null ? null : x.expr.accept(this, o));
        x.expr = _tempexpr;
        return finish(x, o);
    }

    // @ ensures RES!=null
    public Object visitAmbiguousVariableAccess(
        AmbiguousVariableAccess y,
        Object o) {
        {
            ASTNode a = prep(y, o);
            if (a != null) return a;
        }
        AmbiguousVariableAccess x = (AmbiguousVariableAccess) y.clone();
        Name _tempname = (Name) (x.name == null ? null : x.name.accept(this, o));
        x.name = _tempname;
        return finish(x, o);
    }

    // @ ensures RES!=null
    public Object visitVariableAccess(VariableAccess y, Object o) {
        {
            ASTNode a = prep(y, o);
            if (a != null) return a;
        }
        VariableAccess x = (VariableAccess) y.clone();
        return finish(x, o);
    }

    // @ ensures RES!=null
    public Object visitFieldAccess(FieldAccess y, Object o) {
        {
            ASTNode a = prep(y, o);
            if (a != null) return a;
        }
        FieldAccess x = (FieldAccess) y.clone();
        ObjectDesignator _tempod = (ObjectDesignator) (x.od == null ? null
            : x.od.accept(this, o));
        x.od = _tempod;
        return finish(x, o);
    }

    // @ ensures RES!=null
    public Object visitAmbiguousMethodInvocation(
        AmbiguousMethodInvocation y,
        Object o) {
        {
            ASTNode a = prep(y, o);
            if (a != null) return a;
        }
        AmbiguousMethodInvocation x = (AmbiguousMethodInvocation) y.clone();
        Name _tempname = (Name) (x.name == null ? null : x.name.accept(this, o));
        x.name = _tempname;
        TypeModifierPragmaVec _temptmodifiers;
        if (x.tmodifiers == null) {
            _temptmodifiers = null;
        } else {
            _temptmodifiers = TypeModifierPragmaVec.make(x.tmodifiers.size());

            for (int i = 0; i < x.tmodifiers.size(); i++) {
                _temptmodifiers.insertElementAt(
                    (TypeModifierPragma) x.tmodifiers.elementAt(i).accept(
                        this,
                        o),
                    i);
            }
        }
        x.tmodifiers = _temptmodifiers;
        ExprVec _tempargs;
        if (x.args == null) {
            _tempargs = null;
        } else {
            _tempargs = ExprVec.make(x.args.size());

            for (int i = 0; i < x.args.size(); i++) {
                _tempargs.insertElementAt((Expr) x.args.elementAt(i).accept(
                    this,
                    o), i);
            }
        }
        x.args = _tempargs;
        return finish(x, o);
    }

    // @ ensures RES!=null
    public Object visitMethodInvocation(MethodInvocation y, Object o) {
        {
            ASTNode a = prep(y, o);
            if (a != null) return a;
        }
        MethodInvocation x = (MethodInvocation) y.clone();
        ObjectDesignator _tempod = (ObjectDesignator) (x.od == null ? null
            : x.od.accept(this, o));
        x.od = _tempod;
        TypeModifierPragmaVec _temptmodifiers;
        if (x.tmodifiers == null) {
            _temptmodifiers = null;
        } else {
            _temptmodifiers = TypeModifierPragmaVec.make(x.tmodifiers.size());

            for (int i = 0; i < x.tmodifiers.size(); i++) {
                _temptmodifiers.insertElementAt(
                    (TypeModifierPragma) x.tmodifiers.elementAt(i).accept(
                        this,
                        o),
                    i);
            }
        }
        x.tmodifiers = _temptmodifiers;
        ExprVec _tempargs;
        if (x.args == null) {
            _tempargs = null;
        } else {
            _tempargs = ExprVec.make(x.args.size());

            for (int i = 0; i < x.args.size(); i++) {
                _tempargs.insertElementAt((Expr) x.args.elementAt(i).accept(
                    this,
                    o), i);
            }
        }
        x.args = _tempargs;
        return finish(x, o);
    }

    // @ ensures RES!=null
    public Object visitClassLiteral(ClassLiteral y, Object o) {
        {
            ASTNode a = prep(y, o);
            if (a != null) return a;
        }
        ClassLiteral x = (ClassLiteral) y.clone();
        Type _temptype = (Type) (x.type == null ? null : x.type.accept(this, o));
        x.type = _temptype;
        return finish(x, o);
    }

    // @ ensures RES!=null
    public Object visitObjectDesignator(ObjectDesignator y, Object o) {
        return visitASTNode(y, o);
    }

    // @ ensures RES!=null
    public Object visitExprObjectDesignator(ExprObjectDesignator y, Object o) {
        {
            ASTNode a = prep(y, o);
            if (a != null) return a;
        }
        ExprObjectDesignator x = (ExprObjectDesignator) y.clone();
        Expr _tempexpr = (Expr) (x.expr == null ? null : x.expr.accept(this, o));
        x.expr = _tempexpr;
        return finish(x, o);
    }

    // @ ensures RES!=null
    public Object visitTypeObjectDesignator(TypeObjectDesignator y, Object o) {
        {
            ASTNode a = prep(y, o);
            if (a != null) return a;
        }
        TypeObjectDesignator x = (TypeObjectDesignator) y.clone();
        Type _temptype = (Type) (x.type == null ? null : x.type.accept(this, o));
        x.type = _temptype;
        return finish(x, o);
    }

    // @ ensures RES!=null
    public Object visitSuperObjectDesignator(SuperObjectDesignator y, Object o) {
        {
            ASTNode a = prep(y, o);
            if (a != null) return a;
        }
        SuperObjectDesignator x = (SuperObjectDesignator) y.clone();
        return finish(x, o);
    }

    // @ ensures RES!=null
    public Object visitType(Type y, Object o) {
        {
            ASTNode a = prep(y, o);
            if (a != null) return a;
        }
        if (y instanceof javafe.tc.TypeSig) return y;
        return visitASTNode(y, o);
    }

    // @ ensures RES!=null
    public Object visitPrimitiveType(PrimitiveType y, Object o) {
        {
            ASTNode a = prep(y, o);
            if (a != null) return a;
        }
        PrimitiveType x = (PrimitiveType) y.clone();
        TypeModifierPragmaVec _temptmodifiers;
        if (x.tmodifiers == null) {
            _temptmodifiers = null;
        } else {
            _temptmodifiers = TypeModifierPragmaVec.make(x.tmodifiers.size());

            for (int i = 0; i < x.tmodifiers.size(); i++) {
                _temptmodifiers.insertElementAt(
                    (TypeModifierPragma) x.tmodifiers.elementAt(i).accept(
                        this,
                        o),
                    i);
            }
        }
        x.tmodifiers = _temptmodifiers;
        return finish(x, o);
    }

    // @ ensures RES!=null
    public Object visitTypeName(TypeName y, Object o) {
        {
            ASTNode a = prep(y, o);
            if (a != null) return a;
        }
        TypeName x = (TypeName) y.clone();
        TypeModifierPragmaVec _temptmodifiers;
        if (x.tmodifiers == null) {
            _temptmodifiers = null;
        } else {
            _temptmodifiers = TypeModifierPragmaVec.make(x.tmodifiers.size());

            for (int i = 0; i < x.tmodifiers.size(); i++) {
                _temptmodifiers.insertElementAt(
                    (TypeModifierPragma) x.tmodifiers.elementAt(i).accept(
                        this,
                        o),
                    i);
            }
        }
        x.tmodifiers = _temptmodifiers;
        Name _tempname = (Name) (x.name == null ? null : x.name.accept(this, o));
        x.name = _tempname;
        return finish(x, o);
    }

    // @ ensures RES!=null
    public Object visitArrayType(ArrayType y, Object o) {
        {
            ASTNode a = prep(y, o);
            if (a != null) return a;
        }
        ArrayType x = (ArrayType) y.clone();
        TypeModifierPragmaVec _temptmodifiers;
        if (x.tmodifiers == null) {
            _temptmodifiers = null;
        } else {
            _temptmodifiers = TypeModifierPragmaVec.make(x.tmodifiers.size());

            for (int i = 0; i < x.tmodifiers.size(); i++) {
                _temptmodifiers.insertElementAt(
                    (TypeModifierPragma) x.tmodifiers.elementAt(i).accept(
                        this,
                        o),
                    i);
            }
        }
        x.tmodifiers = _temptmodifiers;
        Type _tempelemType = (Type) (x.elemType == null ? null
            : x.elemType.accept(this, o));
        x.elemType = _tempelemType;
        return finish(x, o);
    }

    // @ ensures RES!=null
    public Object visitName(Name y, Object o) {
        return visitASTNode(y, o);
    }

    // @ ensures RES!=null
    public Object visitSimpleName(SimpleName y, Object o) {
        {
            ASTNode a = prep(y, o);
            if (a != null) return a;
        }
        SimpleName x = (SimpleName) y.clone();
        return finish(x, o);
    }

    // @ ensures RES!=null
    public Object visitCompoundName(CompoundName y, Object o) {
        {
            ASTNode a = prep(y, o);
            if (a != null) return a;
        }
        CompoundName x = (CompoundName) y.clone();
        int[] _templocIds = x.locIds;
        x.locIds = _templocIds;
        int[] _templocDots = x.locDots;
        x.locDots = _templocDots;
        return finish(x, o);
    }

    // @ ensures RES!=null
    public Object visitModifierPragma(ModifierPragma y, Object o) {
        return visitASTNode(y, o);
    }

    // @ ensures RES!=null
    public Object visitLexicalPragma(LexicalPragma y, Object o) {
        return visitASTNode(y, o);
    }

    // @ ensures RES!=null
    public Object visitTypeModifierPragma(TypeModifierPragma y, Object o) {
        return visitASTNode(y, o);
    }

    // @ ensures RES!=null
    public Object visitAnOverview(AnOverview y, Object o) {
        return y.clone();
    }

    // @ ensures RES!=null
    public Object visitHoldsStmtPragma(HoldsStmtPragma y, Object o) {
        {
            ASTNode a = prep(y, o);
            if (a != null) return a;
        }
        HoldsStmtPragma x = (HoldsStmtPragma) y.clone();
        ExprVec _tempexpressions;
        if (x.expressions == null) {
            _tempexpressions = null;
        } else {
            _tempexpressions = ExprVec.make(x.expressions.size());

            for (int i = 0; i < x.expressions.size(); i++) {
                _tempexpressions.insertElementAt(
                    (Expr) x.expressions.elementAt(i).accept(this, o),
                    i);
            }
        }
        x.expressions = _tempexpressions;
        return finish(x, o);
    }

    // @ ensures RES!=null
    public Object visitRequiresModifierPragma(RequiresModifierPragma y, Object o) {
        {
            ASTNode a = prep(y, o);
            if (a != null) return a;
        }
        RequiresModifierPragma x = (RequiresModifierPragma) y.clone();
        ExprVec _tempexpressions;
        if (x.expressions == null) {
            _tempexpressions = null;
        } else {
            _tempexpressions = ExprVec.make(x.expressions.size());

            for (int i = 0; i < x.expressions.size(); i++) {
                _tempexpressions.insertElementAt(
                    (Expr) x.expressions.elementAt(i).accept(this, o),
                    i);
            }
        }
        x.expressions = _tempexpressions;
        return finish(x, o);
    }

    // @ ensures RES!=null
    public Object visitGuardedByModifierPragma(
        GuardedByModifierPragma y,
        Object o) {
        {
            ASTNode a = prep(y, o);
            if (a != null) return a;
        }
        GuardedByModifierPragma x = (GuardedByModifierPragma) y.clone();
        ExprVec _tempexpressions;
        if (x.expressions == null) {
            _tempexpressions = null;
        } else {
            _tempexpressions = ExprVec.make(x.expressions.size());

            for (int i = 0; i < x.expressions.size(); i++) {
                _tempexpressions.insertElementAt(
                    (Expr) x.expressions.elementAt(i).accept(this, o),
                    i);
            }
        }
        x.expressions = _tempexpressions;
        return finish(x, o);
    }

    // @ ensures RES!=null
    public Object visitThreadLocalStatusPragma(
        ThreadLocalStatusPragma y,
        Object o) {
        {
            ASTNode a = prep(y, o);
            if (a != null) return a;
        }
        ThreadLocalStatusPragma x = (ThreadLocalStatusPragma) y.clone();
        return finish(x, o);
    }

    // added CF May 2k
    // @ ensures RES!=null
    public Object visitReadOnlyModifierPragma(ReadOnlyModifierPragma y, Object o) {
        {
            ASTNode a = prep(y, o);
            if (a != null) return a;
        }
        ReadOnlyModifierPragma x = (ReadOnlyModifierPragma) y.clone();
        return finish(x, o);
    }

    // @ ensures RES!=null
    public Object visitArrayGuardModifierPragma(
        ArrayGuardModifierPragma y,
        Object o) {
        {
            ASTNode a = prep(y, o);
            if (a != null) return a;
        }
        ArrayGuardModifierPragma x = (ArrayGuardModifierPragma) y.clone();
        ExprVec _tempexpressions;
        if (x.expressions == null) {
            _tempexpressions = null;
        } else {
            _tempexpressions = ExprVec.make(x.expressions.size());

            for (int i = 0; i < x.expressions.size(); i++) {
                _tempexpressions.insertElementAt(
                    (Expr) x.expressions.elementAt(i).accept(this, o),
                    i);
            }
        }
        x.expressions = _tempexpressions;
        return finish(x, o);
    }

    // @ ensures RES!=null
    public Object visitNowarnPragma(NowarnPragma y, Object o) {
        {
            ASTNode a = prep(y, o);
            if (a != null) return a;
        }
        NowarnPragma x = (NowarnPragma) y.clone();
        return finish(x, o);
    }

    // @ ensures RES!=null
    public Object visitGenericArgumentPragma(GenericArgumentPragma y, Object o) {
        {
            ASTNode a = prep(y, o);
            if (a != null) return a;
        }
        GenericArgumentPragma x = (GenericArgumentPragma) y.clone();
        ExprVec _tempexpressions;
        if (x.expressions == null) {
            _tempexpressions = null;
        } else {
            _tempexpressions = ExprVec.make(x.expressions.size());

            for (int i = 0; i < x.expressions.size(); i++) {
                _tempexpressions.insertElementAt(
                    (Expr) x.expressions.elementAt(i).accept(this, o),
                    i);
            }
        }
        x.expressions = _tempexpressions;
        return finish(x, o);
    }

    // @ ensures RES!=null
    public Object visitGenericParameterPragma(GenericParameterPragma y, Object o) {
        {
            ASTNode a = prep(y, o);
            if (a != null) return a;
        }
        GenericParameterPragma x = (GenericParameterPragma) y.clone();
        FormalParaDeclVec _tempargs;
        if (x.args == null) {
            _tempargs = null;
        } else {
            _tempargs = FormalParaDeclVec.make(x.args.size());

            for (int i = 0; i < x.args.size(); i++) {
                _tempargs.insertElementAt(
                    (FormalParaDecl) x.args.elementAt(i).accept(this, o),
                    i);
            }
        }
        x.args = _tempargs;
        return finish(x, o);
    }

    // @ ensures RES!=null
    public Object visitGhostDeclPragma(GhostDeclPragma y, Object o) {
        {
            ASTNode a = prep(y, o);
            if (a != null) return a;
        }
        GhostDeclPragma x = (GhostDeclPragma) y.clone();
        FieldDecl _tempdecl = (FieldDecl) (x.decl == null ? null
            : x.decl.accept(this, o));
        x.decl = _tempdecl;
        return finish(x, o);
    }

}
