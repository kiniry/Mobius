/* Copyright 2000, 2001, Compaq Computer Corporation */

package rcc.tc;

import java.util.Enumeration;

import javafe.ast.*;
import javafe.tc.Env;
import javafe.tc.EnvForLocals;
import javafe.tc.EnvForTypeSig;
import javafe.tc.LookupException;

import javafe.tc.TypeSig;

import javafe.util.*;
import java.io.*;

import rcc.ast.*;
import rcc.ast.TagConstants;
import rcc.tc.Types;
import rcc.tc.*;
import rcc.ast.RccPrettyPrint;

import java.lang.Integer;
import rcc.ast.IntegerVec;

import rcc.ast.TagConstants;
import javafe.ast.*;
import javafe.tc.*;
import javafe.util.*;

// nicer to move that method to some
// utilities class somewhere

public class FlowInsensitiveChecks extends javafe.tc.FlowInsensitiveChecks {

    public static LockStack locks = new LockStack();

    public static EqualsAST equality = new EqualsAST();

    /***************************************************************************
     * * Setup for ghost variables: * *
     **************************************************************************/

    /**
     * * Are we in the middle of processing an annotation?
     * <p> * * (Used by GhostEnv and requires/guarded annotations)
     * <p>
     */
    public static boolean inAnnotation = false;

    public static final ASTDecoration guardDecoration = new ASTDecoration(
            "guard");

    public static final ASTDecoration requiresDecoration = new ASTDecoration(
            "requires");

    public static final ASTDecoration elemGuardDecoration = new ASTDecoration(
            "element guard");

    public static final ASTDecoration threadLocalDecoration = new ASTDecoration(
            "local status");

    // For readonly modifier checking
    private boolean canAssignReadOnly;

    /** Override so that we use GhostEnv instead of EnvForTypeSig * */
    protected EnvForTypeSig makeEnvForTypeSig(TypeSig s, boolean staticContext) {
        EnvForTypeSig env = new GhostEnv(s.getEnv(staticContext), s,
                staticContext);
        return env;
    }

    static public Type getType(VarInit i) {
        return javafe.tc.FlowInsensitiveChecks.getType(i);
    }

    public FlowInsensitiveChecks() {
    }

    public FlowInsensitiveChecks(TypeSig sig, EnvForTypeSig env) {
        this.sig = sig;
        if (env == null) {
            rootSEnv = makeEnvForTypeSig(sig, true);
            rootIEnv = makeEnvForTypeSig(sig, false);
        } else {
            this.rootSEnv = makeEnvForTypeSig(env.getEnclosingClass(), true);
            this.rootIEnv = makeEnvForTypeSig(env.getEnclosingClass(), false);
        }
    }

    /***************************************************************************
     * * Extensions to type declaration member checkers: * *
     **************************************************************************/

    public void checkTypeDeclaration(TypeSig s) {
        Assert.precondition(s.state >= TypeSig.PREPPED);

        // Set up variables for entire traversal
        sig = s;
        rootSEnv = makeEnvForTypeSig(s, true);
        rootIEnv = makeEnvForTypeSig(s, false);

        TypeDecl d = s.getTypeDecl();

        // Process ModifierPragmas
        ExprVec g = ExprVec.make();
        guardDecoration.set((TypeDecl) d, g);

        checkModifierPragmaVec(d.pmodifiers, d, rootSEnv);

        // Process each member declaration
        for (int i = 0, sz = d.elems.size(); i < sz; i++) {
            TypeDeclElem e = d.elems.elementAt(i);
            checkTypeDeclElem(e);
        }
    }

    Env addGhosts(TypeSig sig, Env env) {
        // add any special lock names in here
        return env;
    }

    // @ requires e!=null && sig!=null
    protected void checkTypeDeclElem(TypeDeclElem e) {

        Assert.notNull(sig);
        TypeDecl d = sig.getTypeDecl();
        boolean specOnly = d.specOnly;

        switch (e.getTag()) {

        case TagConstants.FIELDDECL: {
            FieldDecl fd = (FieldDecl) e;
            Env rootEnv = Modifiers.isStatic(fd.modifiers) ? rootSEnv
                    : rootIEnv;
            Env env = addGhosts(sig, rootEnv);

            // Process ModifierPragmas
            boolean staticContext = Modifiers.isStatic(fd.modifiers);
            checkModifierPragmaVec(fd.pmodifiers, fd, env);
            checkTypeModifiers(null, fd.type); // SNF Fri Jul 30 13:24:55 1999

            // Resolve the initializer of a field decl
            if (fd.init != null) {
                leftToRight = true;
                allowedExceptions.removeAllElements();
                Assert.notFalse(allowedExceptions.size() == 0);
                canAssignReadOnly = true;

                locks.mark();
                if (rcc.Main.inst.options().ihl) {
                    if (staticContext) {
                        locks.push(ClassLiteral.make(TypeSig.getSig(fd
                                .getParent()), fd.getStartLoc()));
                    } else {
                        locks.push(ThisExpr.make(sig, fd.getStartLoc()));
                    }
                }
                if (rcc.Main.inst.options().ihnl && staticContext) {
                    locks.push(LiteralExpr.make(TagConstants.NULLLIT, null, fd
                            .getStartLoc()));
                }
                fd.init = checkInit(env, fd.init, fd.type);
                locks.popToMark();
            } else if (Modifiers.isFinal(fd.modifiers) && !specOnly) {
                // Removed for 1.1:
                // ErrorSet.caution(fd.locId,
                // "Final variables must be initialized");
            }
            break;
        }

        case TagConstants.METHODDECL:
        case TagConstants.CONSTRUCTORDECL: {
            RoutineDecl rd = (RoutineDecl) e;
            Env rootEnv = Modifiers.isStatic(rd.modifiers) ? rootSEnv
                    : rootIEnv;
            Env env = addGhosts(sig, rootEnv);
            boolean staticContext = Modifiers.isStatic(rd.modifiers);

            // First do method/constructor specific stuff
            if (rd instanceof MethodDecl) {
                MethodDecl md = (MethodDecl) e;
                checkTypeModifiers(env, md.returnType);
                returnType = md.returnType;
                canAssignReadOnly = false;
                if (md.body != null && !specOnly) {
                    if (Modifiers.isAbstract(md.modifiers))
                        ErrorSet.error(md.loc,
                                "An abstract method cannot include a body");
                    if (Modifiers.isNative(md.modifiers))
                        ErrorSet.error(md.loc,
                                "A native method cannot include a body");
                } else {
                    if (!Modifiers.isAbstract(md.modifiers)
                            && !Modifiers.isNative(md.modifiers) && !specOnly)
                        ErrorSet.error(md.loc,
                                "Method must include a body unless "
                                        + "it is declared abstract or native");
                }
            } else {
                // Constructor
                ConstructorDecl cd = (ConstructorDecl) rd;

                // Was checked in parser
                Assert.notFalse(!(d instanceof InterfaceDecl)); // @ nowarn Pre

                returnType = Types.voidType;
                canAssignReadOnly = true;

                // Check if we need to add an implicit constructor invocation
                // @ assume !specOnly ==> cd.body!=null
                if (!specOnly
                        && !(cd.body.stmts.size() > 0 && cd.body.stmts
                                .elementAt(0) instanceof ConstructorInvocation)) {
                    // no explicit constructor invocation
                    if (sig != Types.javaLangObject()) {
                        // add implicit constructor invocation

                        ExprVec args = ExprVec.make();
                        ConstructorInvocation ci = ConstructorInvocation.make(
                                true, null, Location.NULL,
                                cd.body.locOpenBrace, cd.body.locOpenBrace,
                                args);
                        cd.body.stmts.insertElementAt(ci, 0);
                    }
                }
            }

            // Now do stuff common to methods and constructors

            staticContext = Modifiers.isStatic(rd.modifiers);
            leftToRight = false;
            enclosingLabels.removeAllElements();

            allowedExceptions.removeAllElements();
            for (int j = 0; j < rd.raises.size(); j++) {
                TypeName n = rd.raises.elementAt(j);
                env.resolveType(sig, n);  // TODO: check (rgrig)
                checkTypeModifiers(rootEnv, n);
                allowedExceptions.addElement(TypeSig.getSig(n)); // @ nowarn
                                                                    // Pre
            }
            for (int j = 0; j < rd.args.size(); j++) {
                FormalParaDecl formal = rd.args.elementAt(j);
                PrepTypeDeclaration.inst.checkModifiers(formal.modifiers,
                        Modifiers.ACC_FINAL, formal.getStartLoc(),
                        "formal parameter");
                checkModifierPragmaVec(formal.pmodifiers, formal, env);
                env = new EnvForLocals(env, formal);
                checkTypeModifiers(env, formal.type);
            }

            // Process ModifierPragmas
            checkModifierPragmaVec(rd.pmodifiers, rd, env);

            if (rd.body != null && !specOnly) {
                try {
                    locks.mark();
                    if (Modifiers.isSynchronized(rd.modifiers)) {
                        if (Modifiers.isStatic(rd.modifiers)) {
                            locks.push(ClassLiteral.make(TypeSig.getSig(rd
                                    .getParent()), rd.getStartLoc()));
                        } else {
                            locks.push(ThisExpr.make(sig, rd.getStartLoc()));
                        }
                    } else if (rd instanceof ConstructorDecl) {
                        if (rcc.Main.inst.options().chl) {
                            locks.push(ThisExpr.make(sig, rd.getStartLoc()));
                        }
                    }
                    ExprVec expressions = getRequiresVec(rd);
                    for (int i = 0; i < expressions.size(); i++) {
                        locks.push(expressions.elementAt(i));
                    }
                    checkStmt(env, rd.body);
                } finally {
                    locks.popToMark();
                }
            }
            break;
        }

        case TagConstants.INITBLOCK: {
            locks.mark();
            InitBlock si = (InitBlock) e;
            PrepTypeDeclaration.inst.checkModifiers(si.modifiers,
                    Modifiers.ACC_STATIC, si.getStartLoc(), "initializer body");
            boolean staticContext = Modifiers.isStatic(si.modifiers);
            Env rootEnv = rootSEnv;
            Env env = addGhosts(sig, rootEnv);
            if (rcc.Main.inst.options().ihl) {
                if (staticContext) {
                    locks.push(ClassLiteral.make(
                            TypeSig.getSig(si.getParent()), si.getStartLoc()));
                } else {
                    locks.push(ThisExpr.make(sig, si.getStartLoc()));
                }
            }
            if (rcc.Main.inst.options().ihnl && staticContext) {
                locks.push(LiteralExpr.make(TagConstants.NULLLIT, null, si
                        .getStartLoc()));
            }
            returnType = null;
            canAssignReadOnly = true;
            checkStmt(env, si.block);
            locks.popToMark();
            break;
        }

        case TagConstants.CLASSDECL:
        case TagConstants.INTERFACEDECL: {
            TypeSig.getSig((TypeDecl) e).typecheck();
            break;
        }

        default:
            if (e instanceof TypeDeclElemPragma)
                checkTypeDeclElemPragma((TypeDeclElemPragma) e);
            else
                Assert.fail("Switch fall-through (" + e.getTag() + ")");
        }
    }

    public Env checkModifierPragmaVec(ModifierPragmaVec mod, ASTNode a, Env env) {

        switch (a.getTag()) {
        case TagConstants.METHODDECL:
        case TagConstants.CONSTRUCTORDECL: {
            RoutineDecl rd = (RoutineDecl) a;
            getRequiresVec(rd);
            break;
        }
        case TagConstants.FIELDDECL: {
            FieldDecl fd = (FieldDecl) a;
            getGuardedVec(fd);
            break;
        }
        case TagConstants.CLASSDECL:
        case TagConstants.INTERFACEDECL: {
            getLocalThreadStatus((TypeDecl) a, env);
            break;
        }
        default:
            super.checkModifierPragmaVec(mod, a, env);
            break;
        }
        return env; // TODO: check (rgrig)
    }

    static public ExprVec getRequiresVec(RoutineDecl rd) {
        ExprVec expressions = (ExprVec) requiresDecoration.get(rd);
        if (expressions == null) {
            FlowInsensitiveChecks a = new FlowInsensitiveChecks();
            a.inAnnotation = true;
            a.sig = TypeSig.getSig(rd.parent);
            expressions = a.checkRequiresVec(rd);
            a.inAnnotation = false;
        }
        return expressions;
    }

    static public ExprVec getGuardedVec(FieldDecl fd) {
        ExprVec expressions = (ExprVec) guardDecoration.get(fd);
        if (expressions == null) {
            FlowInsensitiveChecks a = new FlowInsensitiveChecks();
            a.inAnnotation = true;
            if (fd.parent != null) {
                a.sig = TypeSig.getSig(fd.parent);
                expressions = a.checkGuardedVec(fd);
            } else {
                // length field of array
                Assert.notFalse(fd == Types.lengthFieldDecl);
                guardDecoration.set(fd, expressions = ExprVec.make());
            }
            a.inAnnotation = false;
        }
        return expressions;
    }

    static public ExprVec getElemGuardedVec(Type t, Env env) {
        ExprVec expressions = (ExprVec) elemGuardDecoration.get(t);
        if (env == null) {
            env = (Env) Env.typeEnv.get(t);
        }
        if (expressions == null) {
            FlowInsensitiveChecks a = new FlowInsensitiveChecks();
            a.inAnnotation = true;
            a.sig = env.getEnclosingClass(); // SNF
            a.rootSEnv = a.makeEnvForTypeSig(a.sig, true);
            a.rootIEnv = a.makeEnvForTypeSig(a.sig, false);
            // expressions = a.checkElemGuardedVec(t,a.rootIEnv);
            // System.out.println(" " + env.isStaticContext()+ env +
            // env.getEnclosingClass());
            expressions = a.checkElemGuardedVec(t, env);
            a.inAnnotation = false;
        }
        return expressions;
    }

    public Env checkTypeModifierPragmaVec(TypeModifierPragmaVec mod,
            ASTNode a, Env env) {
        getElemGuardedVec((Type) a, env);
        return env; // TODO: check (rgrig)
    }

    protected Env checkTypeModifierPragma(TypeModifierPragma p, ASTNode ctxt,
            Env env) {

        inAnnotation = true; // Must be reset before we exit!
        int tag = p.getTag();
        switch (tag) {
        case TagConstants.ARRAYGUARDMODIFIERPRAGMA: {
            ArrayGuardModifierPragma rp = (ArrayGuardModifierPragma) p;
            checkLockExprVec(env, rp.expressions, rp.getStartLoc());
            if (ctxt.getTag() != TagConstants.ARRAYTYPE) {
                ErrorMsg
                        .print(
                                sig,
                                "Modifiers",
                                ctxt.getStartLoc(),
                                "only array declarations may contain this type of annotation.",
                                Location.NULL);
            }
            ExprVec g = (ExprVec) elemGuardDecoration.get(ctxt);
            for (int i = 0; i < rp.expressions.size(); i++) {
                g.addElement(rp.expressions.elementAt(i));
            }
            break;
        }
        case TagConstants.GENERICARGUMENTPRAGMA:
            // handled in Prep stage
            break;
        default:
            Assert.fail("Unexpected tag " + tag);
        }
        inAnnotation = false;
        return env; // TODO: check (rgrig)
    }

    /***************************************************************************
     * * Extensions to Expr and Stmt checkers: * *
     **************************************************************************/

    protected Env checkStmt(Env env, Stmt s) {
        if (inAnnotation) {
            return env;
        }

        int tag = s.getTag();
        switch (tag) {
        case TagConstants.SYNCHRONIZESTMT:
            try {
                locks.mark();
                SynchronizeStmt ss = (SynchronizeStmt) s;
                ss.expr = checkExpr(env, ss.expr, Types.javaLangObject());
                locks.push(ss.expr);
                env = checkStmt(env, ss.stmt);
            } finally {
                locks.popToMark();
            }
            break;

        case TagConstants.CONSTRUCTORINVOCATION: {
            ConstructorInvocation ci = (ConstructorInvocation) s;
            env = super.checkStmt(env, s);
            if (ci.decl == null)
                return env; // SNF
            if (!inAnnotation) {
                ExprVec expressions = getRequiresVec(ci.decl);
                SubstitutionVec subs = SubstitutionVec.make();
                MultipleSubstitution ms = new MultipleSubstitution(subs);
                checkLocksHeld(ms, expressions, ci.getStartLoc(), "",
                        ci.decl.pmodifiers);
            }
            return env;
        }

        default:
            env = super.checkStmt(env, s);
            break;
        }

        return env;
    }

    protected boolean lockHeld(MultipleSubstitution ms, Expr e) {
        CloneWithSubstitution c = new CloneWithSubstitution(ms);
        e = (Expr) c.clone(e, true);

        // System.out.println (" ---locks "+locks.expressionsToString());
        // System.out.println (" ---expression "+e);

        return locks.contains(e);
    }

    static public rcc.tc.TypeSig defaultInstantiation(rcc.tc.TypeSig sig) {
        boolean t = inAnnotation;
        inAnnotation = true;
        FormalParaDeclVec fpv = (FormalParaDeclVec) PrepTypeDeclaration.typeParametersDecoration
                .get(sig);

        ExprVec args = ExprVec.make();
        if (fpv != null) {
            for (int i = 0; i < fpv.size(); i++) {
                FormalParaDecl parameter = fpv.elementAt(i);
                ExprObjectDesignator eod = ExprObjectDesignator.make(parameter
                        .getStartLoc(), ThisExpr.make(sig, parameter
                        .getStartLoc()));
                FieldAccess fa = FieldAccess.make(eod, parameter.id, parameter
                        .getStartLoc());
                args.addElement(fa);
                sig.getEnv(true).resolveType(sig, parameter.type); // TODO: check (rgrig)
                setType(fa, parameter.type);
                fa.decl = (FieldDecl) PrepTypeDeclaration.parameterDeclDecoration
                        .get(parameter);
                setType(eod.expr, sig); // good enough for now. change below to
                                        // correct sig
            }
        }
        TypeSig s = ((rcc.tc.PrepTypeDeclaration) PrepTypeDeclaration.inst)
                .findTypeSignature(sig.getEnv(true), (rcc.tc.TypeSig) sig,
                        args, sig.getTypeDecl().getStartLoc());

        for (int i = 0; i < args.size(); i++) {
            FieldAccess fa = (FieldAccess) args.elementAt(i);
            setType(((ExprObjectDesignator) fa.od).expr, s);
            s.getEnv(true).resolveType(sig, getType(fa)); // TODO: check (rgrig)
        }

        inAnnotation = t;
        return (rcc.tc.TypeSig) s;
    }

    protected void checkLocksHeld(MultipleSubstitution ms, ExprVec expressions,
            int line, String msg, ModifierPragmaVec mpv) {
        Expr expr;

        // System.out.println ("---locks "+locks.toString());
        // System.out.println ("---substitutions "+ms.toString());
        // System.out.println ("---expressions "+expressions.toString());

        for (int i = 0; i < expressions.size(); i++) {
            if (!lockHeld(ms, expr = expressions.elementAt(i))) {
                ByteArrayOutputStream os = new ByteArrayOutputStream();
                CloneWithSubstitution c = new CloneWithSubstitution(ms);
                int declLoc = getLocInPragmas(expr, mpv);
                expr = (Expr) c.clone(expr, true);
                ErrorMsg.print(sig, "Race", line, "Lock '"
                        + PrettyPrint.inst.toString(expr)
                        + "' may not be held." + "  Locks currently held are '"
                        + locks + "'.", declLoc);
            }
        }
    }

    // version for array access
    protected void checkLocksHeld(MultipleSubstitution ms, ExprVec expressions,
            int line, String msg, TypeModifierPragmaVec mpv) {
        Expr expr;

        for (int i = 0; i < expressions.size(); i++) {
            if (!lockHeld(ms, expr = expressions.elementAt(i))) {
                ByteArrayOutputStream os = new ByteArrayOutputStream();
                CloneWithSubstitution c = new CloneWithSubstitution(ms);
                expr = (Expr) c.clone(expr, true);
                int declLoc = expr.getStartLoc(); // FIX TO PRINT RIGHT LOC
                ErrorMsg.print(sig, "Race", line, "Lock '"
                        + PrettyPrint.inst.toString(expr)
                        + "' may not be held." + "  Locks currently held are '"
                        + locks + "'.", declLoc);
            }
        }
    }

    protected Type modifyEscapingType(Env env, SubstitutionVec s, Type type) {
        MultipleSubstitution ms = new MultipleSubstitution(s);
        CloneWithSubstitution c = new CloneWithSubstitution(ms);

        type = (Type) c.clone(type, true);

        if (type instanceof ArrayType) {
            // recurs for array case. This wastes some work, but the
            // alternative is to make a new clone class.
            ((ArrayType) type).elemType = modifyEscapingType(env, s,
                    ((ArrayType) type).elemType);
            return type;
        }

        if (type instanceof TypeName) {
            type = TypeSig.getSig((TypeName) type);
        }

        if (type instanceof rcc.tc.TypeSig) {
            rcc.tc.TypeSig sig = (rcc.tc.TypeSig) type;
            if (sig.generic != null) {
                CloneForInstantiation ci = new CloneForInstantiation(ms);
                ExprVec args = (ExprVec) ci.clone(sig.expressions, true);
                type = ((rcc.tc.PrepTypeDeclaration) PrepTypeDeclaration.inst)
                        .findTypeSignature(env, sig.generic, args,
                                Location.NULL);
            }
        }

        return type;
    }

    protected void modifyEscapingExpr(Env env, SubstitutionVec s, VarInit e) {
        setType(e, modifyEscapingType(env, s, getType(e)));
    }

    protected Expr checkExpr(Env env, Expr e) {

        if (getTypeOrNull(e) != null)
            // already done
            return e;

        int tag = e.getTag();
        switch (tag) {

        case TagConstants.THISEXPR: {

            ThisExpr t = (ThisExpr) e;

            if (env.isStaticContext() && t.classPrefix == null) {
                ErrorSet.error(e.getStartLoc(),
                        "Unqualified this cannot be used in static contexts");
            }
            Type referredType;

            referredType = sig;
            if (t.classPrefix != null) {
                TypeSig T = (TypeSig) referredType;
                env.resolveType(sig, t.classPrefix); // TODO: check (rgrig)
                referredType = t.classPrefix;
                checkTypeModifiers(env, referredType); // SNF Fri Jul 30
                                                        // 13:36:44 1999

                /*
                 * Check that t.classPrefix is the class of one of our current
                 * instances:
                 */
                TypeSig classPrefix = Types.toClassTypeSig(referredType);
                while (T != null) {
                    if (T == classPrefix)
                        break;
                    if (Modifiers.isStatic(T.getTypeDecl().modifiers))
                        T = null;
                    else
                        T = T.enclosingType;
                }
                if (T == null || (T == sig && env.isStaticContext()))
                    ErrorSet
                            .error(t.getStartLoc(), "Undefined variable: "
                                    + PrettyPrint.inst.toString(referredType)
                                    + ".this");
            }
            Assert.notFalse(referredType != null);
            setType(e, referredType);

            e = super.checkExpr(env, e);
            if (t.classPrefix == null) {
                t.classPrefix = sig;
            }
            return e;
        }

        // Handle accesses to ghost fields as well...
        case TagConstants.FIELDACCESS: {
            if (!inAnnotation) {
                FieldAccess fa = (FieldAccess) e;
                e = super.checkExpr(env, e);
                if (fa.decl == null)
                    return e;
                boolean staticContext = Modifiers.isStatic(fa.decl.modifiers);
                SubstitutionVec s = SubstitutionVec.make();
                if (!staticContext
                        && fa.od.getTag() == TagConstants.EXPROBJECTDESIGNATOR
                        && fa.decl.parent != null) {
                    s.addElement(new Substitution(ThisExpr.make(TypeSig
                            .getSig(fa.decl.parent), fa.od.getStartLoc()),
                            ((ExprObjectDesignator) fa.od).expr));
                }

                modifyEscapingExpr(env, s, e);

                ExprVec expressions = getGuardedVec(fa.decl);
                MultipleSubstitution ms = new MultipleSubstitution(s);
                checkLocksHeld(ms, expressions, fa.getStartLoc(), "",
                        fa.decl.pmodifiers);
                return e;
            }
            // set default result type to integer, in case there is an error
            setType(e, Types.intType);
            FieldAccess fa = (FieldAccess) e;
            Type t = checkObjectDesignator(env, fa.od);
            if (t == null)
                return fa;
            if (t instanceof TypeName)
                t = TypeSig.getSig((TypeName) t);

            try {
                fa.decl = rcc.tc.Types.lookupField(t, fa.id, sig);
            } catch (LookupException ex) {
                reportLookupException(ex, "field", Types.printName(t), fa.locId);
                return fa;
            }
            setType(fa, fa.decl.type);

            if (fa.od instanceof TypeObjectDesignator
                    && !Modifiers.isStatic(fa.decl.modifiers)) {
                if (env.isStaticContext()
                        || ((TypeObjectDesignator) fa.od).type instanceof TypeName)
                    ErrorSet
                            .error(
                                    fa.locId,
                                    "Instance fields may be accessed only via "
                                            + "objects and/or from non-static contexts");
                else
                    ErrorSet.error(fa.locId, "The instance fields of type "
                            + ((TypeObjectDesignator) fa.od).type
                            + " may not be accessed from type " + sig);
            }

            return fa;

        }

        case TagConstants.METHODINVOCATION: {
            e = super.checkExpr(env, e);
            if (e == null)
                return e; // SNF
            if (!inAnnotation) {
                MethodInvocation m = (MethodInvocation) e;
                if (m.decl == null)
                    return e;
                ExprVec expressions = getRequiresVec(m.decl);
                boolean staticContext = Modifiers.isStatic(m.decl.modifiers);
                SubstitutionVec s = SubstitutionVec.make();
                if (!staticContext
                        && m.od.getTag() == TagConstants.EXPROBJECTDESIGNATOR) {
                    s.addElement(new Substitution(ThisExpr.make(TypeSig
                            .getSig(m.decl.parent), m.od.getStartLoc()),
                            ((ExprObjectDesignator) m.od).expr));
                }

                for (int i = 0; i < m.args.size(); i++) {
                    FormalParaDecl parameter = m.decl.args.elementAt(i);
                    Expr expr = m.args.elementAt(i);
                    FieldAccess fa = FieldAccess.make(ExprObjectDesignator
                            .make(parameter.getStartLoc(), ThisExpr.make(
                                    TypeSig.getSig(m.decl.parent), parameter
                                            .getStartLoc())), parameter.id,
                            parameter.getStartLoc());
                    s.addElement(new Substitution(fa, expr));

                    s.addElement(new Substitution(VariableAccess.make(
                            parameter.id, parameter.getStartLoc(), parameter),
                            expr));
                }
                modifyEscapingExpr(env, s, e);

                MultipleSubstitution ms = new MultipleSubstitution(s);
                checkLocksHeld(ms, expressions, m.getStartLoc(), "",
                        m.decl.pmodifiers);
            }
            return e;
        }

        case TagConstants.NEWINSTANCEEXPR: {
            e = super.checkExpr(env, e);
            if (e == null)
                return e; // SNF
            if (!inAnnotation) {
                NewInstanceExpr ne = (NewInstanceExpr) e;
                if (ne.decl == null)
                    return e;
                ExprVec expressions = getRequiresVec(ne.decl);
                SubstitutionVec s = SubstitutionVec.make();

                for (int i = 0; i < ne.args.size(); i++) {
                    FormalParaDecl parameter = ne.decl.args.elementAt(i);
                    Expr expr = ne.args.elementAt(i);
                    FieldAccess fa = FieldAccess.make(ExprObjectDesignator
                            .make(parameter.getStartLoc(), ThisExpr.make(
                                    TypeSig.getSig(ne.decl.parent), parameter
                                            .getStartLoc())), parameter.id,
                            parameter.getStartLoc());
                    s.addElement(new Substitution(fa, expr));

                    s.addElement(new Substitution(VariableAccess.make(
                            parameter.id, parameter.getStartLoc(), parameter),
                            expr));
                }

                modifyEscapingExpr(env, s, e);
                MultipleSubstitution ms = new MultipleSubstitution(s);
                checkLocksHeld(ms, expressions, ne.getStartLoc(), "",
                        ne.decl.pmodifiers);
            }
            return e;
        }

        case TagConstants.CASTEXPR: {
            CastExpr ce = (CastExpr) e;
            ce.expr = checkExpr(env, ce.expr);
            Type exprType = getType(ce.expr);
            env.resolveType(sig, ce.type); // TODO: check (rgrig)
            checkTypeModifiers(env, ce.type); // SNF Fri Jul 30 13:36:44 1999
            if (!Types.isCastable(exprType, ce.type)) {

                if (exprType instanceof TypeName)
                    exprType = TypeSig.getSig((TypeName) exprType);

                if (ce.type instanceof TypeName)
                    ce.type = TypeSig.getSig((TypeName) ce.type);

                if (exprType instanceof ArrayType
                        && ce.type instanceof ArrayType) {
                    if (Types.isCastable(((ArrayType) exprType).elemType,
                            ((ArrayType) ce.type).elemType)) {
                        ErrorMsg.print("BadCast", ce.getStartLoc(),
                                "suspicious cast from '"
                                        + Types.printName(exprType) + "' to '"
                                        + Types.printName(ce.type) + "'",
                                Location.NULL);
                    }
                } else if (exprType instanceof rcc.tc.TypeSig
                        && ce.type instanceof rcc.tc.TypeSig
                        && ((rcc.tc.TypeSig) exprType).generic != null
                        && ((rcc.tc.TypeSig) ce.type).generic != null
                        && ((rcc.tc.TypeSig) exprType).generic == ((rcc.tc.TypeSig) ce.type).generic) {
                    ErrorMsg.print("BadCast", ce.getStartLoc(),
                            "suspicious cast from '"
                                    + Types.printName(exprType) + "' to '"
                                    + Types.printName(ce.type) + "'",
                            Location.NULL);
                } else {
                    ErrorSet.error(ce.locOpenParen, "Bad cast from "
                            + Types.printName(exprType) + " to "
                            + Types.printName(ce.type));
                }
            }
            setType(ce, ce.type);
            return ce;
        }

        case TagConstants.ARRAYREFEXPR: {
            ArrayRefExpr r = (ArrayRefExpr) e;

            r.array = checkExpr(env, r.array);
            Type arrType = getType(r.array);
            r.index = checkExpr(env, r.index);
            Type t = getType(r.index);
            if (arrType instanceof ArrayType) {
                setType(r, ((ArrayType) arrType).elemType);
                Type ndxType = Types.isNumericType(t) ? Types.unaryPromote(t)
                        : t;
                if (!Types.isSameType(ndxType, Types.intType))
                    ErrorSet.error(r.locOpenBracket,
                            "Array index is not an integer");
                if (!inAnnotation) {
                    ExprVec expressions = getElemGuardedVec(arrType, env);

                    MultipleSubstitution ms = new MultipleSubstitution();
                    checkLocksHeld(ms, expressions, r.locOpenBracket, "",
                            arrType.tmodifiers);
                }
            } else {
                setType(r, Types.intType);
                ErrorSet.error(r.locOpenBracket,
                        "Attempt to index an non-array value");
            }

            return r;
        }

        case TagConstants.AMBIGUOUSVARIABLEACCESS: {
            AmbiguousVariableAccess av = (AmbiguousVariableAccess) e;
            Assert.notNull(av.name);
            Expr resolved = env.disambiguateExprName(av.name);
            if (resolved == null) {
                if (av.name.size() == 1)
                    ErrorSet.error(av.getStartLoc(), "Undefined variable '"
                            + av.name.printName() + "'");
                else
                    ErrorSet.error(av.getStartLoc(),
                            "Cannot resolve variable access '"
                                    + av.name.printName() + "'");
                setType(av, Types.intType);
                return av;
            }
            Assert.notFalse(resolved.getTag() != // @ nowarn Pre
                    TagConstants.AMBIGUOUSVARIABLEACCESS);
            return checkExpr(env, resolved);
        }

        default:
            return super.checkExpr(env, e);
        }
    }

    /*
     * //@ requires env!=null && od!=null //@ requires sig!=null protected Type
     * checkObjectDesignator(Env env, ObjectDesignator od, boolean
     * staticContext) {
     * 
     * switch( od.getTag() ) {
     * 
     * case TagConstants.EXPROBJECTDESIGNATOR: { ExprObjectDesignator eod =
     * (ExprObjectDesignator)super. checkObjectDesignator( env, od,
     * staticContext); if (eod != null && eod.expr instanceof ThisExpr) { if
     * (((ThisExpr)eod.expr).classPrefix==null) {
     * ((ThisExpr)eod.expr).classPrefix = sig; } } return eod;
     *  } default: return super. checkObjectDesignator( env, od,
     * staticContext);; } }
     */

    /***************************************************************************
     * * Pragma checkers: * *
     **************************************************************************/

    protected void checkTypeDeclElemPragma(TypeDeclElemPragma e) {
        inAnnotation = true; // Must be reset beforwe exit!
        int tag = e.getTag();

        switch (tag) {
        case TagConstants.GHOSTDECLPRAGMA:
            break;

        default:
            Assert.fail("Unexpected tag " + tag);
        }
        inAnnotation = false;
    }

    protected Expr checkFinalExpr(Env env, Expr expr, int assocLoc) {
        Assert.notFalse(expr != null);
        Expr checkExpr = checkExpr(env, expr, Types.javaLangObject());
        if (!isFinalExpr(env, checkExpr)) {
            ErrorMsg.print(sig, "ConstantLocks", expr.getStartLoc(), "",
                    assocLoc);
        }
        return checkExpr;
    }

    protected void checkLockExprVec(Env env, ExprVec expressions, int assocLoc) {
        for (int i = 0; i < expressions.size(); i++) {
            Expr expr = expressions.elementAt(i);
            Expr checkExpr = checkFinalExpr(env, expr, assocLoc);
            expressions.setElementAt(checkExpr, i);
        }
    }

    protected void addToLockStack(ExprVec expressions) {
        for (int i = 0; i < expressions.size(); i++) {
            Expr expr = expressions.elementAt(i);
            locks.push(expr);
        }
    }

    protected Env checkModifierPragma(ModifierPragma p, ASTNode ctxt, Env env) {

        inAnnotation = true; // Must be reset before we exit!
        int tag = p.getTag();
        switch (tag) {
        case TagConstants.READONLYMODIFIERPRAGMA:
            break;

        case TagConstants.REQUIRESMODIFIERPRAGMA: {
            RequiresModifierPragma rp = (RequiresModifierPragma) p;
            checkLockExprVec(env, rp.expressions, rp.getStartLoc());
            if (ctxt.getTag() != TagConstants.METHODDECL
                    && ctxt.getTag() != TagConstants.CONSTRUCTORDECL) {
                ErrorMsg.print(sig, "Modifiers", ctxt.getStartLoc(),
                        "requires modifiers only allowed on methods.",
                        Location.NULL);
                break;
            }
            ExprVec g = (ExprVec) requiresDecoration.get(ctxt);
            for (int i = 0; i < rp.expressions.size(); i++) {
                g.addElement(rp.expressions.elementAt(i));
            }
            break;
        }
        case TagConstants.GUARDEDBYMODIFIERPRAGMA: {
            if (ctxt.getTag() == TagConstants.CLASSDECL)
                break; // already done
            GuardedByModifierPragma rp = (GuardedByModifierPragma) p;
            checkLockExprVec(env, rp.expressions, rp.getStartLoc());
            if (ctxt.getTag() != TagConstants.FIELDDECL
                    && ctxt.getTag() != TagConstants.CLASSDECL) {
                ErrorMsg
                        .print(
                                sig,
                                "Modifiers",
                                ctxt.getStartLoc(),
                                "guarded_by modifiers only allowed on fields and classes.",
                                Location.NULL);
                break;
            }
            ExprVec g = (ExprVec) guardDecoration.get(ctxt);
            for (int i = 0; i < rp.expressions.size(); i++) {
                Expr expr = rp.expressions.elementAt(i);
                g.addElement(expr);
            }
            break;
        }
        case TagConstants.THREADLOCALSTATUSPRAGMA: {
            if (ctxt.getTag() != TagConstants.CLASSDECL
                    && ctxt.getTag() != TagConstants.INTERFACEDECL) {
                ErrorMsg
                        .print(
                                sig,
                                "ThreadLocal",
                                ctxt.getStartLoc(),
                                "thread_local/thread_shared only allowed on classes and interfaces.",
                                Location.NULL);
                break;
            }
            if (threadLocalDecoration.get(ctxt) != null) {
                ErrorMsg
                        .print(
                                sig,
                                "ThreadLocal",
                                ctxt.getStartLoc(),
                                "only one thread_local/thread_shared modifier allowed per class.",
                                p.getStartLoc());
                break;

            }
            threadLocalDecoration.set(ctxt, new Boolean(
                    ((ThreadLocalStatusPragma) p).local));
            break;
        }
        default:
            Assert.fail("Unexpected tag " + tag);
        }
        inAnnotation = false;
        return env;
    }

    protected Env checkStmtPragma(Env env, StmtPragma s) {
        inAnnotation = true; // Must be reset before we exit!
        int tag = s.getTag();
        switch (tag) {
        case TagConstants.HOLDSSTMTPRAGMA: {
            HoldsStmtPragma cs = (HoldsStmtPragma) s;
            checkLockExprVec(env, cs.expressions, cs.getStartLoc());
            if (rcc.Main.inst.options().pun) {
                for (int i = 0; i < cs.expressions.size(); i++) {
                    Expr e = cs.expressions.elementAt(i);
                    if (locks.contains(e)) {
                        ErrorMsg.print(sig, "Race", e.getStartLoc(), "lock '"
                                + PrettyPrint.inst.toString(e)
                                + "' is already held", Location.NULL);
                    }
                }
            }
            if (!rcc.Main.inst.options().noho) {
                addToLockStack(cs.expressions);
            }
            break;
        }
        default:
            Assert.fail("Unexpected tag " + tag);
        }
        inAnnotation = false;
        return env;
    }

    public ExprVec checkRequiresVec(RoutineDecl rd) {
        ExprVec g = ExprVec.make();

        requiresDecoration.set(rd, g);
        TypeSig s = TypeSig.getSig(rd.parent);

        Assert.precondition(s.state >= TypeSig.PREPPED);

        // Set up variables for entire traversal
        sig = s;
        rootSEnv = makeEnvForTypeSig(s, true); // @ nowarn Invariant
        rootIEnv = makeEnvForTypeSig(s, false); // @ nowarn Invariant
        boolean staticContext = Modifiers.isStatic(rd.modifiers); // 10/28

        Env env = addGhosts(sig, staticContext ? rootSEnv : rootIEnv);

        TypeDecl d = s.getTypeDecl();

        // Process ModifierPragmas
        checkModifierPragmaVec(d.pmodifiers, d, env);

        leftToRight = false;

        // add params
        for (int j = 0; j < rd.args.size(); j++) {
            FormalParaDecl formal = rd.args.elementAt(j);
            PrepTypeDeclaration.inst.checkModifiers(formal.modifiers,
                    Modifiers.ACC_FINAL, formal.getStartLoc(),
                    "formal parameter");
            checkModifierPragmaVec(formal.pmodifiers, formal, env);
            env = new EnvForLocals(env, formal);
        }

        super.checkModifierPragmaVec(rd.pmodifiers, rd, env);

        // check overridden expr ved
        if (rd instanceof MethodDecl) {
            MethodDecl md = (MethodDecl) rd;
            Set methods = javafe.tc.PrepTypeDeclaration.inst.getOverrides(md);
            Enumeration e = methods.elements();
            while (e.hasMoreElements()) {
                MethodDecl m = (MethodDecl) e.nextElement();
                ExprVec superExpressions = (ExprVec) getRequiresVec(m);
                ExprVec expressions = (ExprVec) requiresDecoration.get(rd);
                for (int i = 0; i < expressions.size(); i++) {
                    Expr expr = expressions.elementAt(i);
                    if (!equality.contains(superExpressions, expr)) {
                        int pragmaLoc = getLocInPragmas(expr, rd.pmodifiers);
                        ErrorMsg.print(sig, "Super", rd.locId, "", pragmaLoc);
                    }
                }
            }
        }

        return g;
    }

    protected boolean checkDuplicateExpressions(ExprVec expressions) {
        EqualsASTNoDecl equality = new EqualsASTNoDecl();
        ExprVec es = ExprVec.make();
        for (int i = 0; i < expressions.size(); i++) {
            Expr e = expressions.elementAt(i);
            for (int j = 0; j < es.size(); j++) {
                if (equality.equals(es.elementAt(j), e)) {
                    return true;
                }
            }
            es.addElement(e);
        }
        return false;
    }

    public ExprVec checkGuardedVec(FieldDecl fd) {
        ExprVec g = ExprVec.make();
        guardDecoration.set(fd, g);
        TypeSig s = TypeSig.getSig(fd.parent);

        Assert.precondition(s.state >= TypeSig.PREPPED);

        // Set up variables for entire traversal
        sig = s;
        rootSEnv = makeEnvForTypeSig(s, true); // @ nowarn Invariant
        rootIEnv = makeEnvForTypeSig(s, false); // @ nowarn Invariant
        boolean staticContext = Modifiers.isStatic(fd.modifiers); // 10/28

        Env env = addGhosts(sig, staticContext ? rootSEnv : rootIEnv);

        TypeDecl d = s.getTypeDecl();

        // Process ModifierPragmas
        checkModifierPragmaVec(d.pmodifiers, d, env);
        super.checkModifierPragmaVec(fd.pmodifiers, fd, env);

        if (rcc.Main.inst.options().prg) {
            if (checkDuplicateExpressions(g)) {
                ErrorMsg.print(sig, "Modifiers", fd.getStartLoc(), "field '"
                        + fd.id
                        + "' has redundant guard annotations.  Guards are: '"
                        + PrettyPrint.inst.toString(g) + "'", Location.NULL);
            }
        }

        return g;
    }

    // for type modifiers, we will always be in the current environment.
    public ExprVec checkElemGuardedVec(Type t, Env env) {
        ExprVec g = ExprVec.make();
        elemGuardDecoration.set(t, g);
        super.checkTypeModifierPragmaVec(t.tmodifiers, t, env);

        if (rcc.Main.inst.options().prg) {
            if (checkDuplicateExpressions(g)) {
                ErrorMsg.print(sig, "Modifiers", t.getStartLoc(),
                        "array type has redundant guard annotations.  Guards are: '"
                                + PrettyPrint.inst.toString(g) + "'",
                        Location.NULL);
            }
        }

        return g;
    }

    /***************************************************************************
     * * Utility routines: * *
     **************************************************************************/

    /**
     * * Copy the Type associated with an expression by the typechecking * pass
     * to another Expr. This is used by Substitute to ensure it * returns an
     * Expr of the same Type.
     */
    public static void copyType(VarInit from, VarInit to) {
        Type t = getTypeOrNull(from);
        if (t != null)
            setType(to, t);
    }

    /**
     * * Return a set of *all* the methods a given method overrides.
     * <p> * * This includes transitivity.
     * <p>
     */
    // @ requires md!=null
    // @ ensures RES!=null
    public static Set getAllOverrides(MethodDecl md) {
        Set direct = javafe.tc.PrepTypeDeclaration.inst.getOverrides(md);
        Set result = new Set();

        Enumeration e = direct.elements();
        while (e.hasMoreElements()) {
            MethodDecl directMD = (MethodDecl) (e.nextElement());
            result.add(directMD);
            result.addEnumeration(getAllOverrides(directMD).elements());
        }

        return result;
    }

    /**
     * If <code>rd</code> is a method that overrides a method in a superclass,
     * the overridden method is returned. Otherwise, <code>null</code> is
     * returned.
     */

    public static MethodDecl getSuperClassOverride(RoutineDecl rd) {
        if (!(rd instanceof MethodDecl)) {
            return null;
        }
        MethodDecl md = (MethodDecl) rd;
        MethodDecl override = null;
        Set direct = javafe.tc.PrepTypeDeclaration.inst.getOverrides(md);
        Enumeration e = direct.elements();
        while (e.hasMoreElements()) {
            MethodDecl directMD = (MethodDecl) (e.nextElement());
            if (directMD.parent instanceof ClassDecl) {
                if (override == null) {
                    override = directMD;
                } else {
                    // This suggests that the method is inherited from TWO
                    // classes!
                    // This can actually happen, if the method is one that is
                    // declared in Object, because every interface has the
                    // methods
                    // of Object. In this case, pick the method override that
                    // does not reside in Object.
                    Type javaLangObject = Types.javaLangObject();
                    Type t0 = TypeSig.getSig(override.parent);
                    Type t1 = TypeSig.getSig(directMD.parent);
                    Assert.notFalse(Types.isSameType(t0, javaLangObject)
                            || Types.isSameType(t1, javaLangObject));
                    Assert.notFalse(!Types.isSameType(t0, javaLangObject)
                            || !Types.isSameType(t1, javaLangObject));
                    if (!Types.isSameType(t1, javaLangObject)) {
                        override = directMD;
                    }
                }
            }
        }
        return override;
    }

    /**
     * Returns whether or not <code>rd</code> is a method override
     * declaration, that is, whether or not <code>rd</code> overrides a method
     * declared in a superclass.
     */

    public static boolean isMethodOverride(RoutineDecl rd) {
        return getSuperClassOverride(rd) != null;
    }

    protected boolean isFinalExpr(Env env, Expr expr) {
        switch (expr.getTag()) {
        case TagConstants.VARIABLEACCESS: {
            VariableAccess lva = (VariableAccess) expr;
            return Modifiers.isFinal(lva.decl.modifiers)
                    || readOnlyPragma(lva.decl.pmodifiers) != null;

        }
        case TagConstants.FIELDACCESS: {
            FieldAccess fa = (FieldAccess) expr;
            if (!isFinalObjectDesignator(env, fa.od)) {
                return false;

            }
            try {
                FieldDecl fd = Types.lookupField(getObjectDesignatorType(env,
                        fa.od), fa.id, sig);
                return Modifiers.isFinal(fd.modifiers)
                        || readOnlyPragma(fd.pmodifiers) != null;
            } catch (LookupException le) {
                Assert.fail("can't find field '" + expr + "'");
                return false;
            }
        }
        case TagConstants.THISEXPR:
        case TagConstants.CLASSLITERAL:
        case TagConstants.NULLLIT:
            return true;

        case TagConstants.AMBIGUOUSVARIABLEACCESS:
        default:
            return false;
        }
    }

    private boolean isFinalObjectDesignator(Env env, ObjectDesignator od) {
        switch (od.getTag()) {
        case TagConstants.EXPROBJECTDESIGNATOR: {
            return isFinalExpr(env, ((ExprObjectDesignator) od).expr);
        }

        default:
            return true;
        }
    }

    // assume javafe.tc.flowinsens.checkObjDes has already been called
    protected Type getObjectDesignatorType(Env env, ObjectDesignator od) {

        switch (od.getTag()) {

        case TagConstants.EXPROBJECTDESIGNATOR: {
            ExprObjectDesignator eod = (ExprObjectDesignator) od;
            return getType(eod.expr);
        }

        case TagConstants.TYPEOBJECTDESIGNATOR: {
            TypeObjectDesignator tod = (TypeObjectDesignator) od;
            // Type has been created by disambiguation code, so it is ok.

            Type t = tod.type;
            if (t instanceof TypeName)
                t = TypeSig.getSig((TypeName) t);
            Assert.notFalse(t instanceof TypeSig); // @ nowarn Pre
            return (TypeSig) t;
        }

        case TagConstants.SUPEROBJECTDESIGNATOR: {
            SuperObjectDesignator sod = (SuperObjectDesignator) od;
            TypeDecl d = sig.getTypeDecl();
            TypeSig superSig = TypeSig.getSig(((ClassDecl) d).superClass); // @
                                                                            // nowarn
                                                                            // NonNull
            return superSig;
        }

        default:
            Assert.fail("Fall thru");
            return null; // dummy return
        }
    }

    /** rccwiz support */

    int getLocInPragmas(Expr expr, ModifierPragmaVec mpv) {
        for (int i = 0; i < mpv.size(); i++) {
            ModifierPragma mp = mpv.elementAt(i);
            if (mp instanceof RequiresModifierPragma) {
                RequiresModifierPragma rmp = (RequiresModifierPragma) mp;
                if (rmp.expressions.contains(expr)) {
                    return rmp.getStartLoc();
                }
            } else if (mp instanceof GuardedByModifierPragma) {
                GuardedByModifierPragma gmp = (GuardedByModifierPragma) mp;
                if (gmp.expressions.contains(expr)) {
                    return gmp.getStartLoc();
                }
            }
        }
        return Location.NULL;
    }

    /** *** thread local ********* */

    static public boolean getLocalThreadStatus(TypeDecl d, Env env) {
        Boolean b = (Boolean) threadLocalDecoration.get(d);
        if (b == null) {
            FlowInsensitiveChecks a = new FlowInsensitiveChecks();
            a.sig = TypeSig.getSig(d); // not safe for inner classes
            a.sig.prep(); // different from other cases because we
            // may not have needed to look inside a.sig yet.
            a.inAnnotation = true;
            a.rootSEnv = a.makeEnvForTypeSig(a.sig, true); // @ nowarn
                                                            // Invariant
            a.rootIEnv = a.makeEnvForTypeSig(a.sig, false); // @ nowarn
                                                            // Invariant

            // b = a.checkLocalThreadStatus(d,a.sig.getEnclosingEnv());
            b = a.checkLocalThreadStatus(d, a.rootIEnv);
        }
        return b.booleanValue();
    }

    public Boolean checkLocalThreadStatus(TypeDecl d, Env env) {
        super.checkModifierPragmaVec(d.pmodifiers, d, env);
        Boolean b = ((Boolean) threadLocalDecoration.get(d));

        boolean onCommandLine = rcc.Main.inst != null
                && rcc.Main.inst.commandLineFiles.contains(TypeSig.getSig(d)
                        .getCompilationUnit());

        /* to shortcircuit inference: */
        if (b != null) {
            if (b.booleanValue()) {
                checkThreadLocal(env, d);
            } else {
                checkThreadShared(env, d);
            }
        } else if (rcc.Main.inst.options().dts && onCommandLine) {
            threadLocalDecoration.set(d, new Boolean(false));
            checkThreadShared(env, d);
        } else {
            boolean canBeLocal = isLocalOK(d, env);
            boolean canBeShared = isSharedOK(d, env);
            if (canBeLocal && !canBeShared) {
                threadLocalDecoration.set(d, new Boolean(true));
                checkThreadLocal(env, d);
            } else if (canBeLocal && canBeShared) {
                threadLocalDecoration.set(d, new Boolean(false));
                checkThreadShared(env, d);
            } else if (!canBeLocal && canBeShared) {
                threadLocalDecoration.set(d, new Boolean(false));
                checkThreadShared(env, d);
            } else if (!canBeLocal && !canBeShared) {
                ErrorMsg.print(sig, "ThreadLocal", d.getStartLoc(),
                        "cannot be local or shared", Location.NULL);
                threadLocalDecoration.set(d, new Boolean(true));
            }
        }

        Info
                .out("[infering that "
                        + TypeSig.getSig(d).simpleName
                        + " is "
                        + (((Boolean) threadLocalDecoration.get(d))
                                .booleanValue() ? "thread local"
                                : "thread shared") + "]");

        commonThreadLocal(env, d);

        return ((Boolean) threadLocalDecoration.get(d));
    }

    private boolean guardPragmaExists(ModifierPragmaVec m) {
        if (m == null)
            return false;
        for (int i = 0; i < m.size(); i++) {
            if (m.elementAt(i) instanceof GuardedByModifierPragma) {
                return true;
            }
        }
        return false;
    }

    private ReadOnlyModifierPragma readOnlyPragma(ModifierPragmaVec m) {
        if (m == null)
            return null;
        for (int i = 0; i < m.size(); i++) {
            if (m.elementAt(i) instanceof ReadOnlyModifierPragma) {
                return (ReadOnlyModifierPragma) m.elementAt(i);
            }
        }
        return null;
    }

    private boolean requiresPragmaExists(ModifierPragmaVec m) {
        if (m == null)
            return false;
        for (int i = 0; i < m.size(); i++) {
            if (m.elementAt(i) instanceof RequiresModifierPragma) {
                return true;
            }
        }
        return false;
    }

    private boolean elementGuardPragmaExists(Type a) {
        if (!(a instanceof ArrayType)) {
            return false;
        }
        TypeModifierPragmaVec m = ((ArrayType) a).tmodifiers;
        if (m == null)
            return false;
        for (int i = 0; i < m.size(); i++) {
            if (m.elementAt(i) instanceof ArrayGuardModifierPragma) {
                return true;
            }
        }
        return false;
    }

    private boolean arrayGuarded(Type a) {
        if (!(a instanceof ArrayType)) {
            return true;
        }
        TypeModifierPragmaVec m = ((ArrayType) a).tmodifiers;
        if (m == null)
            return false;
        for (int i = 0; i < m.size(); i++) {
            if (m.elementAt(i) instanceof ArrayGuardModifierPragma) {
                return arrayGuarded(((ArrayType) a).elemType);
            }
        }
        return false;
    }

    public void commonThreadLocal(Env env, TypeDecl d) {
        TypeDeclElem elem;

        for (int i = 0; i < d.elems.size(); i++) {
            elem = d.elems.elementAt(i);
            if (elem.getTag() == TagConstants.FIELDDECL) {
                FieldDecl fd = (FieldDecl) elem;
                if (Modifiers.isStatic(fd.modifiers)) {
                    if (fd.type instanceof TypeSig) {
                        TypeDecl decl = ((TypeSig) fd.type).getTypeDecl();
                        if (getLocalThreadStatus(decl, env)) {
                            ErrorMsg
                                    .print(
                                            sig,
                                            "ThreadLocal",
                                            fd.getStartLoc(),
                                            "the class '"
                                                    + TypeSig.getSig(d)
                                                            .getExternalName()
                                                    + "' must be thread shared because field '"
                                                    + TypeSig.getSig(d)
                                                            .getExternalName()
                                                    + "." + fd.id
                                                    + "' is static",
                                            threadLocalAnnotationLoc(decl));
                        }
                    }
                    if (!Modifiers.isFinal(fd.modifiers)
                            && readOnlyPragma(fd.pmodifiers) == null) {
                        if (!guardPragmaExists(fd.pmodifiers)) {
                            ErrorMsg
                                    .print(
                                            sig,
                                            "StaticField",
                                            fd.getStartLoc(),
                                            "field '"
                                                    + TypeSig.getSig(d)
                                                            .getExternalName()
                                                    + "."
                                                    + fd.id
                                                    + "' must be guarded because it is a non-final static field",
                                            Location.NULL);
                        }
                    }
                }
            }
        }
    }

    int threadLocalAnnotationLoc(TypeDecl d) {
        ModifierPragmaVec mpv = d.pmodifiers;
        if (mpv == null)
            return d.getStartLoc();
        for (int i = 0; i < mpv.size(); i++) {
            ModifierPragma p = mpv.elementAt(i);
            if (p.getTag() == TagConstants.THREADLOCALSTATUSPRAGMA) {
                return p.getStartLoc();
            }
        }
        return d.getStartLoc();
    }

    // TODO: substitute param names from super class for alpha renaming.
    public void checkThreadLocal(Env env, TypeDecl d) {
        TypeDeclElem elem;

        if (Types.isSubclassOf(TypeSig.getSig(d), Types.getJavaLang("Thread"))) {
            ErrorMsg.print(sig, "ThreadLocal", d.getStartLoc(),
                    "java.lang.Thread and its subclasses can not be local",
                    threadLocalAnnotationLoc(d));
        }

        for (int i = 0; i < d.elems.size(); i++) {
            elem = d.elems.elementAt(i);
            switch (elem.getTag()) {
            case TagConstants.FIELDDECL:
                break;
            case TagConstants.METHODDECL: {
                MethodDecl md = (MethodDecl) elem;
                // if ( isMethodOverride(md)) {
                Set methods = javafe.tc.PrepTypeDeclaration.inst
                        .getOverrides(md);

                Enumeration e = methods.elements();
                while (e.hasMoreElements()) {

                    MethodDecl superDecl = (MethodDecl) e.nextElement();
                    if (!getLocalThreadStatus(superDecl.parent, env)) {
                        ErrorMsg.print(sig, "Override", md.getStartLoc(), "'"
                                + md.id.toString() + "'", superDecl
                                .getStartLoc());
                    }
                }
                break;
            }
            // }
            }
        }
    }

    public boolean isLocalOK(TypeDecl d, Env env) {
        TypeDeclElem elem;

        if (d instanceof InterfaceDecl) {
            return false;
        }

        if (d == Types.getJavaLang("Thread").getTypeDecl()) {
            return false;
        }

        for (int i = 0; i < d.elems.size(); i++) {
            elem = d.elems.elementAt(i);
            switch (elem.getTag()) {
            case TagConstants.FIELDDECL: {
                FieldDecl fd = (FieldDecl) elem;
                if (guardPragmaExists(fd.pmodifiers)
                        || elementGuardPragmaExists(((FieldDecl) elem).type)) {
                    return false;
                }
                break;
            }
            case TagConstants.METHODDECL:
                break;
            }
        }
        return true;
    }

    public void checkThreadShared(Env env, TypeDecl d) {
        TypeDeclElem elem;
        boolean unsharedFieldSeen = false;

        if (d instanceof ClassDecl && ((ClassDecl) d).superClass != null) {
            TypeDecl parent = env.resolveTypeName(null, ((ClassDecl) d).superClass) // TODO: check
                    .getTypeDecl();
            if (parent != null && getLocalThreadStatus(parent, env)) {
                ErrorMsg.print(sig, "ThreadLocal", d.getStartLoc(),
                        "super class '"
                                + TypeSig.getSig(parent).getExternalName()
                                + "' of thread shared class '"
                                + TypeSig.getSig(d).getExternalName()
                                + "' must be thread shared", parent
                                .getStartLoc());
            }
        }

        for (int i = 0; i < d.superInterfaces.size(); i++) {
            TypeDecl p = env.resolveTypeName(null, d.superInterfaces.elementAt(i)) // TODO: check
                    .getTypeDecl();
            if (getLocalThreadStatus(p, env)) {
                ErrorMsg.print(sig, "ThreadLocal", d.getStartLoc(),
                        "thread shared class "
                                + TypeSig.getSig(d).getExternalName()
                                + " can not implement thread local interface "
                                + p.id, threadLocalAnnotationLoc(p));
            }
        }

        for (int i = 0; i < d.elems.size(); i++) {
            elem = d.elems.elementAt(i);
            switch (elem.getTag()) {
            case TagConstants.FIELDDECL: {
                FieldDecl fd = (FieldDecl) elem;
                if (!Modifiers.isFinal(fd.modifiers)) {
                    if (!guardPragmaExists(fd.pmodifiers)
                            && readOnlyPragma(fd.pmodifiers) == null) {
                        if (rcc.Main.inst.options().agt) {
                            if (!unsharedFieldSeen) {
                                Info.out("[assuming the unguarded fields of "
                                        + sig + " are guarded by this/" + sig
                                        + ".class]");
                                unsharedFieldSeen = true;
                            }
                            ExprVec expressions = ExprVec.make();
                            if (Modifiers.isStatic(fd.modifiers)) {
                                expressions.addElement(ClassLiteral.make(sig,
                                        fd.getStartLoc()));
                            } else {
                                expressions.addElement(ThisExpr.make(sig, fd
                                        .getStartLoc()));
                            }
                            if (fd.pmodifiers == null) {
                                fd.pmodifiers = ModifierPragmaVec.make();
                            }
                            fd.pmodifiers.addElement(GuardedByModifierPragma
                                    .make(expressions, fd.getStartLoc()));
                        } else {
                            if (!Modifiers.isStatic(fd.modifiers)) {
                                ErrorMsg
                                        .print(
                                                sig,
                                                "SharedField",
                                                fd.getStartLoc(),
                                                "field '"
                                                        + TypeSig
                                                                .getSig(d)
                                                                .getExternalName()
                                                        + "."
                                                        + fd.id
                                                        + "' must be guarded in a thread shared class",
                                                Location.NULL);
                            } else {
                                // error reported by commonThreadLocal method
                            }
                        }
                    }
                }

                unsharedFieldSeen = false; // reuse for arrays
                if (!arrayGuarded(fd.type)) {
                    if (rcc.Main.inst.options().agt) {
                        if (!unsharedFieldSeen) {
                            Info
                                    .out("[assuming the unguarded array elements of "
                                            + sig
                                            + " are guarded by this/"
                                            + sig + ".class]");
                            unsharedFieldSeen = true;
                        }
                        ExprVec expressions = ExprVec.make();
                        if (Modifiers.isStatic(fd.modifiers)) {
                            expressions.addElement(ClassLiteral.make(sig, fd
                                    .getStartLoc()));
                        } else {
                            expressions.addElement(ThisExpr.make(sig, fd
                                    .getStartLoc()));
                        }
                        if (fd.type.tmodifiers == null) {
                            fd.type.tmodifiers = TypeModifierPragmaVec.make();
                        }
                        fd.type.tmodifiers.addElement(ArrayGuardModifierPragma
                                .make(expressions, fd.getStartLoc()));
                    } else {
                        ErrorMsg
                                .print(
                                        sig,
                                        "SharedArray",
                                        fd.getStartLoc(),
                                        "elements of array '"
                                                + TypeSig.getSig(d)
                                                        .getExternalName()
                                                + "."
                                                + fd.id
                                                + "' must be guarded in a thread shared class",
                                        Location.NULL);
                    }
                }

                javafe.tc.TypeSig type = null;
                if (fd.type instanceof TypeName) {
                    type = TypeSig.getSig((TypeName) fd.type);
                    if (type == null) {
                        ErrorMsg.print(sig, "ThreadLocal", fd.getStartLoc(),
                                "cannot find class " + fd.type, Location.NULL);
                        break;
                    }
                }
                if (fd.type instanceof javafe.tc.TypeSig) {
                    type = (javafe.tc.TypeSig) fd.type;
                }
                if (type != null) { // we have a typesig as the type
                    TypeDecl decl = type.getTypeDecl();
                    if (getLocalThreadStatus(decl, env)) {
                        ErrorMsg.print(sig, type, "ThreadLocal", fd
                                .getStartLoc(), "the class '" + type
                                + "' must be thread shared because field '"
                                + TypeSig.getSig(d).getExternalName() + "."
                                + fd.id + "' belongs to a shared class",
                                threadLocalAnnotationLoc(decl));
                    }

                }
                break;
            }
            }
        }
    }

    public boolean isSharedOK(TypeDecl d, Env env) {
        TypeDeclElem elem;

        if (d == Types.getJavaLang("Thread").getTypeDecl()
                || Types.isSubclassOf(TypeSig.getSig(d), Types
                        .getJavaLang("Thread"))) {
            return true;
        }

        if (d == Types.getJavaLang("Object").getTypeDecl()) {
            return true;
        }

        if (d instanceof InterfaceDecl) {
            return true;
        }

        for (int i = 0; i < d.elems.size(); i++) {
            elem = d.elems.elementAt(i);
            switch (elem.getTag()) {
            case TagConstants.FIELDDECL:
                FieldDecl fd = (FieldDecl) elem;
                if (guardPragmaExists(fd.pmodifiers)) {
                    return true;
                }
                break;

            case TagConstants.METHODDECL:
                MethodDecl md = (MethodDecl) elem;
                if (Modifiers.isSynchronized(md.modifiers)
                        || requiresPragmaExists(md.pmodifiers)) {
                    return true;
                }
                break;
            }
        }
        return false;
    }

    /**
     * A precondition of this method is that <code>staticContext</code> be set
     * appropriately.
     */

    protected Expr checkDesignator(Env env, Expr e) {

        e = super.checkDesignator(env, e);

        if (!canAssignReadOnly) {
            // check readonly
            ReadOnlyModifierPragma romp = null;
            // System.out.println("checkDesignator "+e);
            switch (e.getTag()) {
            case TagConstants.VARIABLEACCESS: {
                VariableAccess lva = (VariableAccess) e;
                romp = readOnlyPragma(lva.decl.pmodifiers);
                break;
            }
            case TagConstants.FIELDACCESS: {
                FieldAccess fa = (FieldAccess) e;
                try {
                    FieldDecl fd = Types.lookupField(getObjectDesignatorType(
                            env, fa.od), fa.id, sig);
                    romp = readOnlyPragma(fd.pmodifiers);
                } catch (LookupException le) {
                    Assert.fail("can't find field '" + e + "'");
                }
                break;
            }
            }
            if (romp != null) {
                ErrorMsg.print(sig, "ReadOnly", e.getStartLoc(),
                        "Assigning a variable declared as readonly", romp
                                .getStartLoc());
            }
        }

        return e;
    }
}
