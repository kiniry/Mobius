/* Copyright 2000, 2001, Compaq Computer Corporation */

// Copyright (c) 1999, Compaq Computer Corporation
// Authors: Cormac Flanagan and Rustan Leino.
package rccwizard;

import java.util.Enumeration;
import java.util.Hashtable;

import javafe.ast.ArrayType;
import javafe.ast.ClassDecl;
import javafe.ast.ConstructorDecl;
import javafe.ast.DefaultVisitor;
import javafe.ast.Expr;
import javafe.ast.FieldDecl;
import javafe.ast.FieldDeclVec;
import javafe.ast.GenericVarDecl;
import javafe.ast.MethodDecl;
import javafe.ast.ModifierPragmaVec;
import javafe.ast.Modifiers;
import javafe.ast.RoutineDecl;
import javafe.ast.Type;
import javafe.ast.TypeDecl;
import javafe.tc.ConstantExpr;
import javafe.tc.TypeCheck;
import javafe.tc.TypeSig;
import javafe.tc.Types;
import rcc.ast.ReadOnlyModifierPragma;

public class AnnotationVisitor extends DefaultVisitor {

    /* @ non_null */Hashtable envBase;

    public void visitTypeDecl(TypeDecl x) {
        envBase = new Hashtable();
        if (RccOptions.guessnull) {
            envBase.put("null", Types.javaLangObject());
        }

        Annotator modifierAnnotator = new Annotator(
            "<L",
            x.locId,
            x.id.toString(),
            "type decl",
            "");
        if (!RccOptions.readonly) {
            modifierAnnotator.put("thread_local");
        }
        super.visitTypeDecl(x);
    }

    private boolean isObjectArrayType(Type t) {
        if (!(t instanceof ArrayType)) { return false; }
        return Types.isReferenceType(((ArrayType) t).elemType);
    }

    public void visitRoutineDecl(RoutineDecl rd) {
        String ms;

        // hack to make public methods have no requires clauses:
        // we put this in to check AWT where we didn't have the whole program.
        if (RccOptions.pmnr && Modifiers.isPublic(rd.modifiers)) return;

        if (!(rd instanceof MethodDecl)) {
            ms = "constructor";
            if (rd.implicit) return;
        } else {
            MethodDecl md = (MethodDecl) rd;
            if (Modifiers.isStatic(md.modifiers)) {
                ms = "static method";
                if (md.id.toString().equals("main") && md.args.size() == 1) {
                    GenericVarDecl decl = rd.args.elementAt(0);
                    if (isObjectArrayType(decl.type)) {
                        // main routine, special annotation guesses
                        if (!RccOptions.readonly && RccOptions.guessnull) {
                            Annotator requiresAnnotator = new Annotator(
                                rd,
                                "parameter:" + ms,
                                "requires ");
                            requiresAnnotator.put("null");
                        }
                        return;
                    }
                }
            } else if (!(md.parent instanceof ClassDecl)) {
                ms = "interface method";
            } else if (TypeCheck.inst.getAllOverrides(md).isEmpty()) {
                ms = "instance method";
            } else if (TypeCheck.inst.getOverrides(md) == null) {
                ms = "interface method override";
            } else {
                ms = "class method override";
            }
        }

        Annotator requiresAnnotator = new Annotator(
            rd,
            "parameter:" + ms,
            "requires ");

        boolean isStatic = Modifiers.isStatic(rd.modifiers)
            || rd instanceof ConstructorDecl;
        // @ assume rd.parent != null;
        Hashtable envReq = getEnv(
            rd.parent,
            !isStatic,
            accessLevel(rd.modifiers),
            true,
            false,
            null);

        for (int i = 0; i < rd.args.size(); i++) {
            GenericVarDecl decl = rd.args.elementAt(i);
            // Remove any field named arg; it is not in scope
            if (decl != null) {
                envReq.remove(decl.id.toString());
            }
        }

        for (Enumeration e = envReq.keys(); e.hasMoreElements();) {
            String expr2 = (String) e.nextElement();
            Type type2 = (Type) envReq.get(expr2);

            if (Types.isReferenceType(type2) && !RccOptions.readonly) {
                requiresAnnotator.put(expr2);
            }
        }
    }

    public void visitFieldDecl(FieldDecl fd) {
        String kind = Modifiers.isStatic(fd.modifiers) ? "static field"
            : "instance field";
        String name = fd.id.toString();
        Annotator modifierAnnotator = new Annotator(
            "<<",
            fd.locId,
            name,
            kind,
            "");

        if (Modifiers.isFinal(fd.modifiers)) { return; }

        if (RccOptions.readonly) {
            modifierAnnotator.put("readonly");
        }

        // @ assume fd.parent != null;
        Hashtable env = getEnv(
            fd.parent,
            !Modifiers.isStatic(fd.modifiers),
            0,
            !isConstantFinal(fd),
            false,
            null);

        for (Enumeration e = env.keys(); e.hasMoreElements();) {
            String expr2 = (String) e.nextElement();
            Type type2 = (Type) env.get(expr2);

            if (Types.isReferenceType(type2) && !RccOptions.readonly) {
                modifierAnnotator.put("guarded_by " + expr2);
            }
        }
    }

    // @ ensures RES != null;
    // @ ensures RES.keyType == type(String);
    // @ ensures RES.elementType == type(Type);
    private Hashtable getEnv(
        /* @ non_null */TypeDecl td,
        boolean allowInstance,
        int accessLevel,
        boolean allowConstantFinals,
        boolean returnNonConstantNames,
        FieldDecl fdUpto) {
        Hashtable env = (Hashtable) envBase.clone();

        // @ assume env.keyType == type(String);
        // @ assume env.elementType == type(Type);

        TypeSig sig = TypeSig.getSig(td);
        FieldDeclVec fds = sig.getFields(true); // rgrig: include inherited.
        // TODO: check

        if (allowInstance) {
            env.put("this", sig);
        } else {
            env.put(td.id + ".class", Types.javaLangObject());
        }

        for (int i = 0; i < fds.size(); i++) {
            FieldDecl fd = fds.elementAt(i);
            // @ assume fd.parent != null;

            // Consider adding fd to env

            if (fd == fdUpto) { return env; }

            if (!returnNonConstantNames && !Modifiers.isFinal(fd.modifiers)
                && readOnlyPragma(fd.pmodifiers) == null) {
                continue;
            }

            if (!allowInstance && !Modifiers.isStatic(fd.modifiers))
            // Dont include instance field
                continue;

            if (accessLevel(fd.modifiers) < accessLevel)
            // Field is more private than the reference to it would be
                continue;

            TypeSig fdsig = TypeSig.getSig(fd.parent);
            if (!TypeCheck.inst.canAccess(
                sig,
                fdsig,
                fd.modifiers,
                fd.pmodifiers))
            // Cannot access the field
                continue;

            if (!allowConstantFinals && isConstantFinal(fd)) {
                continue;
            }

            // Ok, add field to env
            env.put(fd.id.toString(), fd.type);

        }

        return env;
    }

    private boolean isConstantFinal(FieldDecl fd) {
        return Modifiers.isFinal(fd.modifiers) && fd.init != null
            && fd.init instanceof Expr
            && ConstantExpr.eval((Expr) fd.init) != null;
    }

    /**
     * Returns an integer corresponding to the access modifiers in "modifiers".
     */

    private int accessLevel(int modifiers) {
        // TBW: also check for spec_public
        if (Modifiers.isPrivate(modifiers)) return 0;
        if (Modifiers.isProtected(modifiers)) return 2;
        if (Modifiers.isPublic(modifiers)) return 3;
        return 1;
    }

    private ReadOnlyModifierPragma readOnlyPragma(ModifierPragmaVec m) {
        if (m == null) return null;
        for (int i = 0; i < m.size(); i++) {
            if (m.elementAt(i) instanceof ReadOnlyModifierPragma) { return (ReadOnlyModifierPragma) m.elementAt(i); }
        }
        return null;
    }

}
