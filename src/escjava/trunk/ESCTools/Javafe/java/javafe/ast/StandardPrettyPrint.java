/* Copyright 2000, 2001, Compaq Computer Corporation */

package javafe.ast;

import java.io.OutputStream;
import java.io.ByteArrayOutputStream;
import java.io.IOException;
import javafe.util.Assert;
import javafe.util.Location;

public class StandardPrettyPrint extends PrettyPrint {

    public StandardPrettyPrint() { }

    //@ requires self != null
    public StandardPrettyPrint(PrettyPrint self) { super(self); }

    public void print(OutputStream o, CompilationUnit cu) {
        if (cu == null) {
            writeln(o, "<null CompilationUnit>");
            return;
        }
        if (cu.lexicalPragmas != null) {
            for (int i = 0; i < cu.lexicalPragmas.size(); i++)
                self.print(o, cu.lexicalPragmas.elementAt(i));
            writeln(o);
        }
        if (cu.pkgName != null) {
            write(o, "package "); self.print(o, cu.pkgName); writeln(o, ";");
            writeln(o);
        }
        if (cu.imports.size() > 0) {
            for(int j=0; j<cu.imports.size(); j++) {
                ImportDecl i = cu.imports.elementAt(j);
                write(o, "import ");
                if (i instanceof SingleTypeImportDecl)
                    self.print(o, ((SingleTypeImportDecl)i).typeName);
                else {
                    self.print(o, ((OnDemandImportDecl)i).pkgName);	//@ nowarn Cast
                    write(o, ".*");
                }
                writeln(o, ";");
            }
            writeln(o);
        }
        for(int j=0; j<cu.elems.size(); j++) {
            self.print(o, 0, cu.elems.elementAt(j));
            writeln(o);
        }
    }

    public void printnoln(OutputStream o, int ind, TypeDecl d) {
        if (d == null) {
            write(o, "<null TypeDecl>");
            return;
        }

        if (d.specOnly) {
            writeln(o);
            spaces(o, ind);
            writeln(o, "/* Only specification information is available for "
                    + "this type */");
            writeln(o);
            spaces(o, ind);
        }
	
        if (d.pmodifiers != null)
            for (int i = 0; i < d.pmodifiers.size(); i++) {
                self.print(o, ind, d.pmodifiers.elementAt(i));
                writeln(o);
                spaces(o, ind);
            }
        String mod = Modifiers.toString(d.modifiers);
        if (!mod.equals("")) {
            writeln(o, mod);
            spaces(o, ind);
        }

        Identifier id;

        switch (d.getTag()) {
      
            case TagConstants.CLASSDECL:
                {
                    ClassDecl cd = (ClassDecl)d;
                    writeln(o, "class "+(id=cd.id));
                    if (cd.superClass!=null) {
                        if (!toString(cd.superClass).equals("java.lang.Object")
                            || PrettyPrint.displayInferred) {
                            spaces(o, ind);
                            write(o, "extends ");
                            self.print(o, cd.superClass);
                            writeln(o);
                        }
                    }
                    if (cd.superInterfaces.size()!=0) {
                        spaces(o, ind);
                        write(o, "implements ");
                        self.print(o, cd.superInterfaces);
                        writeln(o);
                    }
                    break;
                }
      
            case TagConstants.INTERFACEDECL:
                {
                    InterfaceDecl cd = (InterfaceDecl)d;
                    writeln(o, "interface "+(id=cd.id));
                    if (cd.superInterfaces.size() != 0) {
                        spaces(o, ind);
                        write(o, "extends ");
                        self.print(o, cd.superInterfaces);
                        writeln(o,"");
                    }
                    break;
                }

            default:
                spaces(o, ind);
                writeln(o, unknownTag(d));
                id = Identifier.intern("?");
        }

        spaces(o, ind);
        writeln(o, "{");
        for (int i = 0; i < d.elems.size(); i++) {
            TypeDeclElem elem = d.elems.elementAt(i);
            //@ assume elem.hasParent   // "invariant"
            spaces(o, ind+INDENT);
            self.print(o, ind+INDENT, elem, id, true);
            if (i != d.elems.size()-1) writeln(o);
        }
        spaces(o, ind);
        write(o, "}");
    }

    public void print(OutputStream o, int ind, Stmt s) {
        if (s == null) {
            writeln(o, "<null Stmt>");
            return;
        }

        switch (s.getTag()) {
      
            case TagConstants.RETURNSTMT: 
                {
                    ReturnStmt r = (ReturnStmt)s;
                    if (r.expr == null)
                        write(o, "return;");
                    else {
                        write(o, "return ");
                        self.print(o, ind, r.expr);
                        write(o, ';');
                    }
                    return;
                }
      
            case TagConstants.THROWSTMT: 
                {
                    ThrowStmt t = (ThrowStmt)s;
                    write(o, "throw "); self.print(o, ind, t.expr); write(o, ';');
                    return;
                }
      
            case TagConstants.ASSERTSTMT: {
                AssertStmt a = (AssertStmt)s;
                write(o, "assert "); self.print(o, ind, a.pred); //write(o, ")");
                if (a.label != null) {
                    write(o, " : ");
                    self.print(o, ind, a.label);
                }
                write(o, ";");
                return;
            }
      
            case TagConstants.SWITCHSTMT: 
                {
                    SwitchStmt c = (SwitchStmt)s;
                    write(o, "switch ("); self.print(o, ind, c.expr); write(o, ") ");
                    // Fall through
                }

            case TagConstants.BLOCKSTMT: 
                {
                    GenericBlockStmt b = (GenericBlockStmt)s;
                    int nextInd = ind + INDENT;
                    writeln(o, "{");
                    boolean lastWasLabel = false;
                    for(int i = 0; i < b.stmts.size(); i++) {
                        Stmt sub = b.stmts.elementAt(i);
                        if (sub.getTag() == TagConstants.SWITCHLABEL) {
                            SwitchLabel x = (SwitchLabel)sub;
                            if (x.expr == null && sub.getStartLoc() == b.locCloseBrace) {
                                // this is an implicit "default: break;" statement
                                Assert.notFalse(i == b.stmts.size() - 2); //@ nowarn Pre
                                // don't print this statement or the next, which should be
                                // a "break"
                                Assert.notFalse(b.stmts.elementAt(i+1).getTag() //@ nowarn Pre
                                                == TagConstants.BREAKSTMT);
                                if (!PrettyPrint.displayInferred)
                                    break;
                            }
                            if (i != 0 && ! lastWasLabel) writeln(o);
                            if (x.expr == null) { spaces(o, ind); writeln(o, "default:"); }
                            else {
                                spaces(o, ind);
                                write(o, "case ");
                                self.print(o, ind, x.expr);
                                writeln(o, ":");
                            }
                            lastWasLabel = true;
                        } else {
                            spaces(o, nextInd);
                            self.print(o, nextInd, sub);
                            writeln(o);
                            lastWasLabel = false;
                        }
                    }
                    spaces(o, ind);
                    write(o, '}');
                    return;
                }
      
            case TagConstants.WHILESTMT: 
                {
                    WhileStmt w = (WhileStmt)s;
                    write(o, "while ("); self.print(o, ind, w.expr); write(o, ") ");
                    self.print(o, ind, w.stmt);
                    return;
                }
      
            case TagConstants.DOSTMT: 
                {
                    DoStmt d = (DoStmt)s;
                    write(o, "do ");
                    self.print(o, ind, d.stmt);
                    write(o, " while ("); self.print(o, ind, d.expr); write(o, ");");
                    return;
                }
      
            case TagConstants.IFSTMT: 
                {
                    IfStmt i = (IfStmt)s;
                    write(o, "if ("); self.print(o, ind, i.expr); write(o, ") ");
                    self.print(o, ind, i.thn);
                    if (! (i.els.getTag() == TagConstants.SKIPSTMT)) {
                        write(o, '\n');
                        spaces(o, ind); write(o, "else "); self.print(o, ind, i.els);
                    }
                    return;
                }
      
            case TagConstants.BREAKSTMT: 
                {
                    BreakStmt b = (BreakStmt)s;
                    if (b.label == null) write(o, "break;");
                    else {
                        write(o, "break ");
                        write(o, b.label.toString());
                        write(o, ';');
                    }
                    return;
                }
      
            case TagConstants.CONTINUESTMT: 
                {
                    ContinueStmt c = (ContinueStmt)s;
                    if (c.label == null) write(o, "continue;");
                    else {
                        write(o, "continue ");
                        write(o, c.label.toString());
                        write(o, ';');
                    }
                    return;
                }
      
            case TagConstants.SYNCHRONIZESTMT: 
                {
                    SynchronizeStmt x = (SynchronizeStmt)s;
                    if (x.stmt.getTag() == TagConstants.BLOCKSTMT) {
                        write(o, "synchronized (");
                        self.print(o, ind, x.expr);
                        write(o, ") ");
                        self.print(o, ind, x.stmt);
                    } else {
                        write(o, "synchronized (");
                        self.print(o, ind, x.expr);
                        write(o, ") {\n");
                        spaces(o, ind+INDENT);
                        self.print(o, ind+INDENT, x.stmt);
                        spaces(o, ind);
                        write(o, '}');
                    }
                    return;
                }
      
            case TagConstants.EVALSTMT: 
                {
                    EvalStmt x = (EvalStmt)s;
                    self.print(o, ind, x.expr); write(o, ';');
                    return;
                }
      
            case TagConstants.LABELSTMT: 
                {
                    LabelStmt x = (LabelStmt)s;
                    write(o, x.label.toString());
                    write(o, ": ");
                    self.print(o, ind, x.stmt);
                    return;
                }
      
            case TagConstants.SKIPSTMT: 
                write(o, ';');
                return;
      
            case TagConstants.TRYFINALLYSTMT: 
                {
                    TryFinallyStmt x = (TryFinallyStmt)s;
                    if (x.tryClause.getTag() == TagConstants.TRYCATCHSTMT)
                        self.print(o, ind, x.tryClause);
                    else if (x.tryClause instanceof BlockStmt) {
                        write(o, "try ");
                        self.print(o, ind, x.tryClause);
                    } else {
                        write(o, "try {\b");
                        spaces(o, ind);
                        self.print(o, ind+INDENT, x.tryClause);
                        spaces(o, ind);
                        write(o, '}');
                    }
        
                    if (x.finallyClause.getTag() == TagConstants.BLOCKSTMT) {
                        write(o, " finally ");
                        self.print(o, ind, x.finallyClause);
                    } else {
                        write(o, " finally {\n");
                        spaces(o, ind);
                        self.print(o, ind+INDENT, x.finallyClause);
                        spaces(o, ind);
                        write(o, '}');
                    }
                    return;
                }
      
            case TagConstants.TRYCATCHSTMT: 
                {
                    TryCatchStmt x = (TryCatchStmt)s;
                    if (x.tryClause.getTag() == TagConstants.BLOCKSTMT) {
                        write(o, "try ");
                        self.print(o, ind, x.tryClause);
                    } else {
                        write(o, "try {\n");
                        spaces(o, ind+INDENT);
                        self.print(o, ind+INDENT, x.tryClause);
                        spaces(o, ind);
                        write(o, '}');
                    }
        
                    for(int i = 0; i < x.catchClauses.size(); i++) {
                        CatchClause c = x.catchClauses.elementAt(i);
                        write(o, " catch ("); self.print(o, c.arg); write(o, ") ");
                        self.print(o, ind, c.body);
                    }
                    return;
                }
      
            case TagConstants.CLASSDECLSTMT: 
                {
                    ClassDecl x = ((ClassDeclStmt)s).decl;
                    self.printnoln(o, ind, x);
                    return;
                }
      
            case TagConstants.VARDECLSTMT: 
                {
                    LocalVarDecl x = ((VarDeclStmt)s).decl;
                    self.print(o, ind, x, true);
                    return;
                }
      
            case TagConstants.FORSTMT: 
                {
                    ForStmt x = (ForStmt)s;
                    write(o, "for (");
        
                    if (x.forInit.size() > 0)
                        if (x.forInit.elementAt(0).getTag() == TagConstants.VARDECLSTMT) {
                            self.print(o, ((VarDeclStmt)x.forInit.elementAt(0))//@nowarn Cast
                                       .decl.type);
                            write(o, ' ');
                            for(int i = 0; i < x.forInit.size(); i++) {
                                VarDeclStmt d = (VarDeclStmt)x.forInit.elementAt(i); //@nowarn Cast
                                write(o, d.decl.id.toString());
                                if (d.decl.init != null) {
                                    write(o, '=');
                                    self.print(o, ind, d.decl.init);
                                }
                                if (i+1 < x.forInit.size()) write(o, ", ");
                            }
                        } else
                            for(int i = 0; i < x.forInit.size(); i++) {
                                EvalStmt e = (EvalStmt) x.forInit.elementAt(i); //@nowarn Cast
                                self.print(o, ind, e.expr);
                                if (i+1 < x.forInit.size()) write(o, ", ");
                            }
                    write(o, "; ");
                    self.print(o, ind, x.test);
                    write(o, "; ");
                    for(int i = 0; i < x.forUpdate.size(); i++) {
                        self.print(o, ind, x.forUpdate.elementAt(i));
                        if (i+1 < x.forUpdate.size()) write(o, ", ");
                    }
                    write(o, ") ");
                    self.print(o, ind, x.body);
                    return;
                }
      
            case TagConstants.CONSTRUCTORINVOCATION: {
                ConstructorInvocation x = (ConstructorInvocation)s;
                if (x.enclosingInstance != null) {
                    if (!(x.enclosingInstance instanceof ThisExpr) ||
                        !(((ThisExpr)x.enclosingInstance).inferred) ||
                        PrettyPrint.displayInferred) {
                        self.print(o, ind, x.enclosingInstance);
                        write(o, ".");
                    }
                }
                write(o, (x.superCall ? "super" : "this"));
                self.print(o, ind, x.args);
                write(o, ';');
                return;
            }

            case TagConstants.SWITCHLABEL: {
                /*
                 * This case never happens unless a client directly calls us on
                 * a SwitchLabel; normally block and switch statements handle
                 * switch labels directly for better formating (multiple
                 * cases/line).
                 */
                SwitchLabel x = (SwitchLabel)s;

                if (x.expr == null)
                    writeln(o, "default:");
                else {
                    write(o, "case ");
                    self.print(o, ind, x.expr);
                    writeln(o, ":");
                }
                return;
            }

            default:
                if (s instanceof StmtPragma)
                    self.print(o, ind, (StmtPragma)s);
                else write(o, unknownTag(s));
                return;
        }
    }

    public void print(OutputStream o, int ind, TypeDeclElem d, 
                      Identifier classId, boolean showBody) {
        if (d == null) {
            writeln(o, "<null TypeDeclElem>");
            return;
        }
        switch( d.getTag() ) {
      
            case TagConstants.FIELDDECL:
                self.print(o, ind, (FieldDecl)d, showBody); writeln(o);
                break;

            case TagConstants.INITBLOCK:
                {
                    if (showBody) {
                        InitBlock si = (InitBlock)d;
                        write(o, Modifiers.toString(si.modifiers));
                        if (si.pmodifiers != null)
                            for (int i = 0; i < si.pmodifiers.size(); i++) {
                                write(o, ' ');
                                self.print(o, ind, si.pmodifiers.elementAt(i));
                            }
                        self.print(o, ind, si.block);
                        writeln(o);
                    }
                    break;
                }

            case TagConstants.METHODDECL:
                {
                    MethodDecl md = (MethodDecl)d;
        
                    if (md.id.toString().equals("<clinit>")) {
                        break;
                    }
        
                    write(o, Modifiers.toString(md.modifiers));
                    self.print(o, md.returnType);
                    write(o, ' ');
                    write(o, md.id.toString());
                    self.print(o, ind, md.args);
                    if (md.raises.size() != 0)
                    { write(o, " throws "); self.print(o, md.raises); }
                    if (md.pmodifiers != null) {
                        for (int i = 0; i < md.pmodifiers.size(); i++) {
                            writeln(o);
                            spaces(o, ind+1);
                            self.print(o, ind, md.pmodifiers.elementAt(i));
                        }
                        write(o, ' ');
                    }
                    displayBody(o,ind, md.body, showBody,
                                d.getParent().specOnly,
                                "method");
                    break;
                }
        
            case TagConstants.CONSTRUCTORDECL:
                {
                    ConstructorDecl md = (ConstructorDecl)d;

                    // Don't print default constructors:
                    if (md.implicit && !PrettyPrint.displayInferred) {
                        // need to at least do a <newline> here!
                        writeln(o, "// <default constructor>");
                        break;
                    }

                    write(o, Modifiers.toString(md.modifiers));
                    write(o, classId.toString());
                    self.print(o, ind, md.args);
                    if (md.raises.size() != 0)
                    { write(o, " throws "); self.print(o, md.raises); }
                    if (md.pmodifiers != null) {
                        for (int i = 0; i < md.pmodifiers.size(); i++) {
                            writeln(o);
                            spaces(o, ind+1);
                            self.print(o, ind, md.pmodifiers.elementAt(i));
                        }
                        write(o, ' ');
                    }

                    displayBody(o, ind, md.body, showBody,
                                d.getParent().specOnly,
                                "constructor");
                    break;
                }

            case TagConstants.CLASSDECL:
            case TagConstants.INTERFACEDECL:
                {
                    self.print(o, ind, (TypeDecl)d);
                    break;
                }

            default:
                if (d instanceof TypeDeclElemPragma)
                    self.print(o, ind, (TypeDeclElemPragma)d);
                else writeln(o, unknownTagMsg(d.getTag()));
                break;
        }
    }


    //@ requires o != null
    void displayBody(OutputStream o, int ind, BlockStmt body,
		     boolean showBody, boolean specOnly, String kind) {
	if (!showBody || body==null) {
	    writeln(o, ";");
	    return;
	}

	writeln(o);
	spaces(o, ind);

	if (specOnly) {
	    writeln(o,"{");
	    spaces(o, ind);
	    writeln(o, "  /* " + kind + " body unavailable */");
	    spaces(o, ind);
	    writeln(o,"}");
	} else {
            self.print(o, ind, body);
	    writeln(o);
	}
    }

     
    public void print(OutputStream o, TypeNameVec tns) {
        if (tns == null) write(o, "<null TypeNameVec>");
        else
            for( int i=0; i<tns.size(); i++ ) {
                if (i != 0) write(o, ", ");
                self.print(o, tns.elementAt(i));
            }
    }

    public void print(OutputStream o, int ind, FormalParaDeclVec fps) {
        if (fps == null) write(o, "<null FormalParaDeclVec>");
        else {
            write(o, '(');
            for (int i=0; i<fps.size(); i++) {
                if (i != 0) write(o, ", ");

                FormalParaDecl d = fps.elementAt(i);
                write(o, Modifiers.toString(d.modifiers));
                self.print(o, d);
                if (d.pmodifiers != null)
                    for (int j = 0; j < d.pmodifiers.size(); j++) {
                        write(o, ' ');
                        self.print(o, ind, d.pmodifiers.elementAt(j));
                    }
            }
            write(o, ')');
        }
    }

    public void print(OutputStream o, int ind, ExprVec es) {
        if (es == null) write(o, "<null ExprVec>");
        else {
            write(o, '(');
            for (int i = 0; i < es.size(); i++) {
                if (i != 0) write(o, ", ");
                self.print(o, ind, es.elementAt(i));
            }
            write(o, ')');
        }
    }

    public void print(OutputStream o, GenericVarDecl d) {
        if (d == null) write(o, "<null GenericVarDecl>");
        else {
            self.print(o, d.type);
            write(o, ' ');
            write(o, d.id.toString());
        }
    }
  
    public void print(OutputStream o, int ind, LocalVarDecl d,
                      boolean showBody) {
        if (d == null) write(o, "<null VarDecl>");
        else {
            write(o, Modifiers.toString(d.modifiers));
            self.print(o, d.type);
            write(o, ' ');
            write(o, d.id.toString());
            if (showBody && d.init != null)
            { write(o, " = "); self.print(o, ind, d.init); }
            if (d.pmodifiers != null)
                for (int i = 0; i < d.pmodifiers.size(); i++) {
                    write(o, ' ');
                    self.print(o, ind, d.pmodifiers.elementAt(i));
                }
            write(o, ';');
        }
    }
  
    public void print(OutputStream o, int ind, FieldDecl d, boolean showBody) {
        if (d == null) write(o, "<null VarDecl>");
        else {
            write(o, Modifiers.toString(d.modifiers));
            self.print(o, d.type);
            write(o, ' ');
            write(o, d.id.toString());
            if (showBody && d.init != null)
            { write(o, " = "); self.print(o, ind, d.init); }
            if (d.pmodifiers != null)
                for (int i = 0; i < d.pmodifiers.size(); i++) {
                    write(o, ' ');
                    self.print(o, ind, d.pmodifiers.elementAt(i));
                }
            write(o, ';');
        }
    }
  
    public void print(OutputStream o, Type t) {
        if (t == null) { write(o, "<null Type>"); return; }
        switch (t.getTag()) {
            case TagConstants.BOOLEANTYPE: write(o, "boolean"); break;
            case TagConstants.BYTETYPE: write(o, "byte"); break;
            case TagConstants.ERRORTYPE: write(o, "error"); break;
            case TagConstants.SHORTTYPE: write(o, "short"); break;
            case TagConstants.INTTYPE: write(o, "int"); break;
            case TagConstants.LONGTYPE: write(o, "long"); break;
            case TagConstants.CHARTYPE: write(o, "char"); break;
            case TagConstants.FLOATTYPE: write(o, "float"); break;
            case TagConstants.DOUBLETYPE: write(o, "double"); break;
            case TagConstants.VOIDTYPE: write(o, "void"); break;
            case TagConstants.NULLTYPE: write(o, "null"); break;
            case TagConstants.TYPENAME:
                self.print(o, ((TypeName)t).name); break;
            case TagConstants.ARRAYTYPE:
                self.print(o, ((ArrayType)t).elemType); write(o, "[");
                write(o,"]");
                break;
            default:
                write(o, t.toString() );
                break;
        }
        print(o, 2, t.tmodifiers);
    }
  
    public void print(OutputStream o, Name n) {
        if (n == null) write(o, "<null Name>");
        else write(o, n.printName());
    }
  
    static public void println(VarInit e) {
	inst.print(System.out,0,e);
	System.out.println("");
    }

    public void print(OutputStream o, int ind, VarInit e) {
        if (e == null) {
            write(o, "<null expression>");
            return;
        }

        int eTag = e.getTag();
        switch (eTag) {
      
            case TagConstants.ARRAYINIT: 
                {
                    VarInitVec v = ((ArrayInit)e).elems;
                    write(o, "{ ");
                    for(int i = 0; i < v.size(); i++) {
                        if (i!=0 ) write(o, ", ");
                        self.print(o, ind, v.elementAt(i));
                    }
                    write(o, " }");
                    return;
                }
                    
            case TagConstants.THISEXPR: {
                ThisExpr t = (ThisExpr)e;
                if (t.classPrefix!=null) {
                    self.print(o, t.classPrefix);
                    write(o, ".");
                }
                write(o, "this");
                return;
            }

                // Literals
            case TagConstants.BOOLEANLIT: 
            case TagConstants.STRINGLIT:
            case TagConstants.CHARLIT:
            case TagConstants.DOUBLELIT: 
            case TagConstants.FLOATLIT:
            case TagConstants.INTLIT:
            case TagConstants.LONGLIT:
                write(o, toCanonicalString(eTag, ((LiteralExpr)e).value));
                return;

            case TagConstants.NULLLIT:
                write(o, "null");
                return;

            case TagConstants.ARRAYREFEXPR:
                {
                    ArrayRefExpr r = (ArrayRefExpr)e;
                    self.print(o, ind, r.array);
                    write(o, '['); self.print(o, ind, r.index); write(o, ']');
                    return;
                }

            case TagConstants.NEWINSTANCEEXPR:
                { 
                    NewInstanceExpr ne = (NewInstanceExpr)e;
                    if (ne.enclosingInstance != null) {
                        if (!(ne.enclosingInstance instanceof ThisExpr) ||
                            !(((ThisExpr)ne.enclosingInstance).inferred) ||
                            PrettyPrint.displayInferred) {
                            self.print(o, ind, ne.enclosingInstance);
                            write(o, ".");
                        }
                    }
                    write(o, "new "); self.print(o, ne.type); self.print(o, ind, ne.args);
                    if (ne.anonDecl != null) {
                        writeln(o, " {");
                        for (int i = 0; i < ne.anonDecl.elems.size(); i++) {
                            TypeDeclElem elem = ne.anonDecl.elems.elementAt(i);
                            //@ assume elem.hasParent   // "invariant"
                            spaces(o, ind+INDENT);
                            self.print(o, ind+INDENT, elem, ne.anonDecl.id, true);
                            if (i != ne.anonDecl.elems.size()-1) writeln(o);
                        }
                        spaces(o, ind);
                        write(o, "}");
                    }
                    return;
                }

            case TagConstants.NEWARRAYEXPR:
                {
                    NewArrayExpr na = (NewArrayExpr)e;
                    Type basetype = na.type;
                    int cnt;

                    for (cnt = 0; basetype.getTag() == TagConstants.ARRAYTYPE; cnt++) {
                        basetype = ((ArrayType)basetype).elemType;
                    }
                    write(o, "new "); self.print(o, basetype);
                    for(int i=0; i<na.dims.size(); i++) {
                        write(o, '[');
                        if (na.init == null) {
                            self.print(o, ind, na.dims.elementAt(i));
                        }
                        write(o, ']');
                    }
                    for ( ; 0 < cnt; cnt--) write(o, "[]");
                    if (na.init != null) self.print(o, ind, na.init);
                    return;
                }

            case TagConstants.CONDEXPR:
                {
                    CondExpr ce = (CondExpr)e;
                    self.print(o, ind, ce.test); write(o, " ? ");
                    self.print(o, ind, ce.thn); write(o, " : ");
                    self.print(o, ind, ce.els);
                    return;
                }

            case TagConstants.INSTANCEOFEXPR:
                {
                    InstanceOfExpr ie = (InstanceOfExpr)e;
                    self.print(o, ind, ie.expr);
                    write(o, " instanceof ");
                    self.print(o, ie.type);
                    return;
                }

            case TagConstants.CASTEXPR:
                {
                    CastExpr ce = (CastExpr)e;
                    write(o, '('); self.print(o, ce.type); write(o, ')');
                    self.print(o, ind, ce.expr);
                    return;
                }

            case TagConstants.CLASSLITERAL:
                {
                    ClassLiteral cl = (ClassLiteral)e;
                    self.print(o, cl.type); write(o, ".class");
                    return;
                }

                // Binary expressions
            case TagConstants.OR: case TagConstants.AND:
            case TagConstants.BITOR: case TagConstants.BITXOR:
            case TagConstants.BITAND: case TagConstants.NE:
            case TagConstants.EQ: case TagConstants.GE:
            case TagConstants.GT: case TagConstants.LE:
            case TagConstants.LT: case TagConstants.LSHIFT:
            case TagConstants.RSHIFT: case TagConstants.URSHIFT:
            case TagConstants.ADD: case TagConstants.SUB:
            case TagConstants.DIV: case TagConstants.MOD:
            case TagConstants.STAR:
            case TagConstants.ASSIGN: case TagConstants.ASGMUL:
            case TagConstants.ASGDIV: case TagConstants.ASGREM:
            case TagConstants.ASGADD: case TagConstants.ASGSUB:
            case TagConstants.ASGLSHIFT: case TagConstants.ASGRSHIFT:
            case TagConstants.ASGURSHIFT: case TagConstants.ASGBITAND:
            case TagConstants.ASGBITOR: case TagConstants.ASGBITXOR:
                {
                    BinaryExpr be = (BinaryExpr)e;
                    self.print(o, ind, be.left); write(o, ' ');
                    write(o, OperatorTags.toString(be.op)); write(o, ' ');
                    self.print(o, ind, be.right);
                    return;
                }

                // Unary expressions
            case TagConstants.UNARYSUB: case TagConstants.UNARYADD:
            case TagConstants.NOT: case TagConstants.BITNOT:
            case TagConstants.INC: case TagConstants.DEC:
            case TagConstants.POSTFIXINC: case TagConstants.POSTFIXDEC:
                {
                    UnaryExpr ue = (UnaryExpr)e;
                    if (ue.op == TagConstants.POSTFIXINC)
                    { self.print(o, ind, ue.expr); write(o, "++"); }
                    else if (ue.op == TagConstants.POSTFIXDEC)
                    { self.print(o, ind, ue.expr); write(o, "--"); }
                    else {
                        write(o, OperatorTags.toString(ue.op));
                        write(o, " "); self.print(o, ind, ue.expr);
                    }
                    return;
                }

            case TagConstants.PARENEXPR:
                {
                    ParenExpr pe = (ParenExpr)e;
                    write(o, '('); self.print(o, ind, pe.expr); write(o, ')');
                    return;
                }

            case TagConstants.AMBIGUOUSVARIABLEACCESS:
                self.print(o, ((AmbiguousVariableAccess)e).name);
                return;

            case TagConstants.VARIABLEACCESS:
                {
                    VariableAccess lva = (VariableAccess)e;
                    write(o, lva.decl.id.toString());
                    return;
                }
      
            case TagConstants.FIELDACCESS:
                {
                    FieldAccess a = (FieldAccess)e;
                    self.print(o, ind, a.od); write(o, a.id.toString());
                    return;
                }
      
            case TagConstants.AMBIGUOUSMETHODINVOCATION:
                {
                    AmbiguousMethodInvocation ie = (AmbiguousMethodInvocation)e;
                    self.print(o, ie.name); self.print(o, ind, ie.args);
                    return;
                }

            case TagConstants.METHODINVOCATION:
                {
                    MethodInvocation ie = (MethodInvocation)e;
                    self.print(o, ind, ie.od);
                    write(o, ie.id.toString());
                    self.print(o, ind, ie.args);
                    return;
                }

            default:
                write(o, unknownTag(e));
                return;
        }
    }

    public void print(OutputStream o, int ind, ObjectDesignator od) {
        if (od == null) { write(o, "<null object designator>"); return; }
        switch (od.getTag()) {
            case TagConstants.EXPROBJECTDESIGNATOR:
                {
                    ExprObjectDesignator a = (ExprObjectDesignator)od;
                    if (a.expr.getTag() != TagConstants.THISEXPR
                        || !((ThisExpr)a.expr).inferred
                        || PrettyPrint.displayInferred)
                    { self.print(o, ind, a.expr); write(o, '.'); }
                    return;
                }
      
            case TagConstants.TYPEOBJECTDESIGNATOR:
                {
                    TypeObjectDesignator a = (TypeObjectDesignator)od;
                    if (a.type.getTag() == TagConstants.TYPENAME
                        || PrettyPrint.displayInferred)
                    { self.print(o, a.type); write(o, '.'); }
                    return;
                }
      
            case TagConstants.SUPEROBJECTDESIGNATOR:
                write(o, "super.");
                return;
      
            default:
                write(o, unknownTag(od));
                break;
        }
    }

    //// toString methods

    /**
     * Requires that <code>tag</code> is one of constants on the left of this
     * table:
     * <center><code><table>
     * <tr> <td> TagConstants.BOOLEANLIT </td> <td> Boolean </td> </tr>
     * <tr> <td> TagConstants.CHARLIT </td>   <td> Integer </td> </tr>
     * <tr> <td> TagConstants.DOUBLELIT </td> <td> Double </td> </tr>
     * <tr> <td> TagConstants.FLOATLIT </td>  <td> Float </td> </tr>
     * <tr> <td> TagConstants.INTLIT </td>    <td> Integer </td> </tr>
     * <tr> <td> TagConstants.LONGLIT </td>   <td> Long </td> </tr>
     * <tr> <td> TagConstants.STRINGLIT </td> <td> String </td> </tr>
     * </center></code></table>
     * 
     * and that <code>val</code> is an instance of the corresponding type
     * on the right.
     * @return a canonical text representation for literal values.
     */

    /*@ requires ((tag==TagConstants.BOOLEANLIT) ||
      @           (tag==TagConstants.INTLIT) ||
      @           (tag==TagConstants.LONGLIT) ||
      @           (tag==TagConstants.FLOATLIT) ||
      @           (tag==TagConstants.DOUBLELIT) ||
      @           (tag==TagConstants.STRINGLIT) ||
      @           (tag==TagConstants.CHARLIT));
      @*/
    /*@ requires (((tag==TagConstants.BOOLEANLIT) ==> (val instanceof Boolean)) &&
      @           ((tag==TagConstants.INTLIT) ==> (val instanceof Integer)) &&
      @           ((tag==TagConstants.LONGLIT) ==> (val instanceof Long)) &&
      @           ((tag==TagConstants.FLOATLIT) ==> (val instanceof Float)) &&
      @           ((tag==TagConstants.DOUBLELIT) ==> (val instanceof Double)) &&
      @           ((tag==TagConstants.STRINGLIT) ==> (val instanceof String)) &&
      @           ((tag==TagConstants.CHARLIT) ==> (val instanceof Integer)));
      @*/
    //@ ensures \result != null
    public static String toCanonicalString(int tag, Object val) {
        if (tag == TagConstants.BOOLEANLIT) return val.toString();

        if (tag == TagConstants.DOUBLELIT) {
            String s = val.toString();
            if (s.equals("Infinity")) return "1.0 / 0.0";
            if (s.equals("-Infinity")) return "-1.0 / 0.0";
            if (s.equals("NaN")) return "0.0d / 0.0";
            return val.toString() + "D";
        }

        if (tag == TagConstants.FLOATLIT) {
            String s = val.toString();
            if (s.equals("Infinity")) return "1.0f / 0.0f";
            if (s.equals("-Infinity")) return "-1.0f / 0.0f";
            if (s.equals("NaN")) return "0.0f / 0.0f";
            return val.toString() + "F";
        }

        if (tag == TagConstants.INTLIT) {
            int v = ((Integer) val).intValue();
            if (v == Integer.MIN_VALUE) return "0x80000000";
            else if (v < 0) return "0x" + Integer.toHexString(v);
            else return Integer.toString(v);
        }

        if (tag == TagConstants.LONGLIT) {
            long v = ((Long) val).longValue();
            if (v == Long.MIN_VALUE) return "0x8000000000000000L";
            else if (v < 0) return "0x" + Long.toHexString(v) + "L";
            else return Long.toString(v) + "L";
        }

        if (tag == TagConstants.CHARLIT || tag == TagConstants.STRINGLIT) {
            char quote;
            if (tag == TagConstants.CHARLIT) {
                quote = '\'';
                val = new Character((char)((Integer)val).intValue());
            } else quote = '\"';
            String s = val.toString();
            StringBuffer result = new StringBuffer(s.length()+2);
            result.append(quote);
            for(int i = 0, len = s.length(); i < len; i++) {
                char c = s.charAt(i);
                switch (c) {
                    case '\b': result.append("\\b"); break;
                    case '\t': result.append("\\t"); break;
                    case '\n': result.append("\\n"); break;
                    case '\f': result.append("\\f"); break;
                    case '\r': result.append("\\r"); break;
                    case '\"': result.append("\\\""); break;
                    case '\'': result.append("\\'"); break;
                    case '\\': result.append("\\\\"); break;
                    default:
                        if (32 <= c && c < 128) result.append(c);
                        else {
                            result.append("\\u");
                            for(int j=12; j>=0; j-=4)
                                result.append(Character.forDigit((c>>j)&0xf, 16));
                        }
                }
            }
            result.append(quote);
            return result.toString();
        }    

        Assert.precondition(false);
        return null; // Dummy
    }

    public void print(OutputStream o, LexicalPragma lp) {
        write(o, "// Lexical pragma at " + lp.getStartLoc() + " ");
        writeln(o, lp.toString());
    }

    public void print(OutputStream o, int ind, TypeDeclElemPragma tp) {
        spaces(o, ind);
        write(o, "// TypeDeclElemPragma pragma at " + tp.getStartLoc() + " ");
        write(o, tp.toString());
    }

    public void print(OutputStream o, int ind, ModifierPragma mp) {
        write(o, "// ModifierPragma pragma at " + mp.getStartLoc() + " ");
        write(o, mp.toString());
    }

    public void print(OutputStream o, int ind, StmtPragma sp) {
        spaces(o, ind);
        write(o, "// StmtPragma pragma at " + sp.getStartLoc() + " ");
        write(o, sp.toString());
    }


    public void print(OutputStream o, int ind, TypeModifierPragma tp) {
        spaces(o, ind);
        write(o, "// TypeModifierPragma pragma at " + tp.getStartLoc() + " ");
        write(o, tp.toString());
    }
  
    //@ requires o != null
    public void print(OutputStream o, int ind, TypeModifierPragmaVec t) {
        if (t != null) {
            for (int i = 0; i < t.size(); i++) {
                write(o, ' ');
                self.print(o, ind, t.elementAt(i));
            }
        }
    }
  
    /**
     * Generate text to describe a ASTNote with an unknown tag
     */
    //@ requires n != null
    //@ ensures \result != null
    public String unknownTag(ASTNode n) {
        return unknownTagMsg(n.getTag());
    }
  
    /**
     * Generate text to describe a given unknown tag
     */
    //@ ensures \result != null
    public String unknownTagMsg(int tag) {
        return "UnknownTag<" + tag + ":"
            + PrettyPrint.inst.toString(tag) + ">";
    }
}
