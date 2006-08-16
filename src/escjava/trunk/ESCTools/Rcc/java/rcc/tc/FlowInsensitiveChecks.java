/* Copyright 2000, 2001, Compaq Computer Corporation */

package rcc.tc;

import java.util.Enumeration;

import javafe.ast.ASTDecoration;
import javafe.ast.ASTNode;
import javafe.ast.ArrayRefExpr;
import javafe.ast.ArrayType;
import javafe.ast.ClassDecl;
import javafe.ast.ClassLiteral;
import javafe.ast.ConstructorDecl;
import javafe.ast.ConstructorInvocation;
import javafe.ast.Expr;
import javafe.ast.ExprObjectDesignator;
import javafe.ast.ExprVec;
import javafe.ast.FieldAccess;
import javafe.ast.FieldDecl;
import javafe.ast.FormalParaDecl;
import javafe.ast.FormalParaDeclVec;
import javafe.ast.InitBlock;
import javafe.ast.InterfaceDecl;
import javafe.ast.LiteralExpr;
import javafe.ast.MethodDecl;
import javafe.ast.MethodInvocation;
import javafe.ast.ModifierPragma;
import javafe.ast.ModifierPragmaVec;
import javafe.ast.Modifiers;
import javafe.ast.NewInstanceExpr;
import javafe.ast.ObjectDesignator;
import javafe.ast.PrettyPrint;
import javafe.ast.RoutineDecl;
import javafe.ast.Stmt;
import javafe.ast.StmtPragma;
import javafe.ast.SynchronizeStmt;
import javafe.ast.ThisExpr;
import javafe.ast.Type;
import javafe.ast.TypeDecl;
import javafe.ast.TypeDeclElem;
import javafe.ast.TypeDeclElemPragma;
import javafe.ast.TypeModifierPragma;
import javafe.ast.TypeModifierPragmaVec;
import javafe.ast.TypeName;
import javafe.ast.TypeObjectDesignator;
import javafe.ast.VarInit;
import javafe.ast.VariableAccess;
import javafe.tc.Env;
import javafe.tc.EnvForEnclosedScope;
import javafe.tc.EnvForLocals;
import javafe.tc.EnvForTypeSig;
import javafe.tc.LookupException;
import javafe.tc.TypeSig;
import javafe.util.Assert;
import javafe.util.ErrorSet;
import javafe.util.Info;
import javafe.util.Location;
import javafe.util.Set;
import rcc.RccOptions;
import rcc.ast.ArrayGuardModifierPragma;
import rcc.ast.CloneForInstantiation;
import rcc.ast.CloneWithSubstitution;
import rcc.ast.EqualsAST;
import rcc.ast.EqualsASTNoDecl;
import rcc.ast.ErrorMsg;
import rcc.ast.GuardedByModifierPragma;
import rcc.ast.HoldsStmtPragma;
import rcc.ast.MultipleSubstitution;
import rcc.ast.ReadOnlyModifierPragma;
import rcc.ast.RequiresModifierPragma;
import rcc.ast.Substitution;
import rcc.ast.SubstitutionVec;
import rcc.ast.TagConstants;
import rcc.ast.ThreadLocalStatusPragma;

public class FlowInsensitiveChecks extends javafe.tc.FlowInsensitiveChecks {

    public static LockStack locks = new LockStack();

    public static EqualsAST equality = new EqualsAST();

    // === Setup for ghost variables ===

    /** Whether we are or not in an annotation. */
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

    /** We use <code>GhostEnv</code> instead of <code>EnvForTypeSig</code>. */
    protected EnvForTypeSig makeEnvForTypeSig(TypeSig s, boolean staticContext) {
        return new GhostEnv(s.getEnv(staticContext), s, staticContext);
    }

    // TODO: Comment this.
    public FlowInsensitiveChecks() {
    // Do nothing.
    }

    // TODO: Comment this.
    public FlowInsensitiveChecks(TypeSig sig, EnvForTypeSig env) {
        this.sig = sig;

        TypeSig ts = sig;
        if (env != null) {
            ts = env.getEnclosingClass();
        }
        rootSEnv = makeEnvForTypeSig(ts, true);
        rootIEnv = makeEnvForTypeSig(ts, false);
    }

    // === Extensions to type declaration member checkers ===

    // TODO: Comment this!
    // requires s.state >= TypeSig.PREPPED;
    public void checkTypeDeclaration(/* @ non_null */TypeSig s) {
        Assert.precondition(s.state >= TypeSig.PREPPED);

        // Set up variables for entire traversal
        sig = s;
        rootSEnv = makeEnvForTypeSig(s, true);
        rootIEnv = makeEnvForTypeSig(s, false);

        TypeDecl d = s.getTypeDecl();

        // Process ModifierPragmas
        ExprVec g = ExprVec.make();
        guardDecoration.set(d, g);

        checkModifierPragmaVec(d.pmodifiers, d, rootSEnv);

        // Process each member declaration
        for (int i = 0, sz = d.elems.size(); i < sz; i++) {
            TypeDeclElem e = d.elems.elementAt(i);
            checkTypeDeclElem(e);
        }
    }

    // TODO: Comment this!
    private Env addGhosts(TypeSig tsig, Env env) {
        // add any special lock names in here
        return env;
    }

    // TODO: Comment this!
    // TODO: It looks like it could pay of to turn this into a template
    // method or something similar. There is a lot of common processing
    // but also pieces specific to universes (in javafe) and rcc (here).
    // Note that there are also some ESC/Java specific checks tangled in
    // the javafe code.
    // TODO: Abstract the computation of the root environment.
    // @ requires e != null && sig != null;
    protected void checkTypeDeclElem(/* @ non_null */TypeDeclElem e) {
        Assert.notNull(sig);
        Assert.notFalse(sig.state >= TypeSig.PREPPED);
        boolean staticContext;
        TypeDecl d = sig.getTypeDecl();
        boolean specOnly = d.specOnly;

        switch (e.getTag()) {

        case TagConstants.FIELDDECL: {
            FieldDecl fd = (FieldDecl) e;
            staticContext = Modifiers.isStatic(fd.modifiers);
            Env rootEnv = staticContext ? rootSEnv : rootIEnv;
            Env env = addGhosts(sig, rootEnv);

            // Process ModifierPragmas
            staticContext = Modifiers.isStatic(fd.modifiers);
            checkModifierPragmaVec(fd.pmodifiers, fd, env);
            checkTypeModifiers(env, fd.type);

            // Resolve the initializer of a field decl
            if (fd.init != null) {
                leftToRight = true;
                allowedExceptions.removeAllElements();
                Assert.notFalse(allowedExceptions.size() == 0);

                // begin rcc-specific code
                canAssignReadOnly = true;
                locks.mark();
                if (RccOptions.get().ihl) {
                    if (staticContext) {
                        locks.push(ClassLiteral.make(
                            TypeSig.getSig(fd.getParent()),
                            fd.getStartLoc()));
                    } else {
                        locks.push(ThisExpr.make(sig, fd.getStartLoc()));
                    }
                }
                if (RccOptions.get().ihnl && staticContext) {
                    locks.push(LiteralExpr.make(
                        TagConstants.NULLLIT,
                        null,
                        fd.getStartLoc()));
                }
                fd.init = checkInit(env, fd.init, fd.type);
                locks.popToMark();
                // end rcc-specific code
            }
            break;
        }

        case TagConstants.METHODDECL:
        case TagConstants.CONSTRUCTORDECL: {
            RoutineDecl rd = (RoutineDecl) e;
            staticContext = Modifiers.isStatic(rd.modifiers);
            Env rootEnv = staticContext ? rootSEnv : rootIEnv;
            Env env = addGhosts(sig, rootEnv);

            // First do method/constructor specific stuff
            if (rd instanceof MethodDecl) {
                MethodDecl md = (MethodDecl) e;
                checkTypeModifiers(env, md.returnType);
                returnType = md.returnType;
                canAssignReadOnly = false;
                if (md.body != null && !specOnly) {
                    if (Modifiers.isAbstract(md.modifiers))
                        ErrorSet.error(
                            md.loc,
                            "An abstract method cannot include a body");
                    if (Modifiers.isNative(md.modifiers))
                        ErrorSet.error(
                            md.loc,
                            "A native method cannot include a body");
                }
            } else {
                // Constructor
                ConstructorDecl cd = (ConstructorDecl) rd;

                // Was checked in parser
                Assert.notFalse(!(d instanceof InterfaceDecl)); // @ nowarn Pre

                returnType = Types.voidType;
                canAssignReadOnly = true;

                // rgrig: This has been updated in Javafe
                // Check if we need to add an implicit constructor invocation
                // @ assume !specOnly ==> cd.body != null
                if (!specOnly
                    && !(cd.body.stmts.size() > 0 && cd.body.stmts.elementAt(0) instanceof ConstructorInvocation)) {
                    // no explicit constructor invocation
                    if (sig != Types.javaLangObject()) {
                        // add implicit constructor invocation

                        ExprVec args = ExprVec.make();
                        ConstructorInvocation ci = ConstructorInvocation.make(
                            true,
                            null,
                            Location.NULL,
                            cd.body.locOpenBrace,
                            cd.body.locOpenBrace,
                            args);
                        cd.body.stmts.insertElementAt(ci, 0);
                    }
                }
            }

            // Now do stuff common to methods and constructors
            leftToRight = false;
            enclosingLabels.removeAllElements();

            allowedExceptions.removeAllElements();
            for (int j = 0; j < rd.raises.size(); j++) {
                TypeName n = rd.raises.elementAt(j);
                env.resolveType(sig, n);
                checkTypeModifiers(env, n);
                allowedExceptions.addElement(TypeSig.getSig(n)); // @ nowarn
                // Pre
            }

            env = new EnvForEnclosedScope(env);
            for (int j = 0; j < rd.args.size(); j++) {
                FormalParaDecl formal = rd.args.elementAt(j);
                PrepTypeDeclaration.getInst().checkModifiers(
                    formal.modifiers,
                    Modifiers.ACC_FINAL,
                    formal.getStartLoc(),
                    "formal parameter");
                checkModifierPragmaVec(formal.pmodifiers, formal, rootEnv);
                env = new EnvForLocals(env, formal);
                checkTypeModifiers(env, formal.type);
            }

            // Process ModifierPragmas
            env = checkModifierPragmaVec(rd.pmodifiers, rd, env);

            if (rd.body != null && !specOnly) {
                try {
                    // begin rcc-specific code
                    locks.mark();
                    if (Modifiers.isSynchronized(rd.modifiers)) {
                        if (Modifiers.isStatic(rd.modifiers)) {
                            locks.push(ClassLiteral.make(
                                TypeSig.getSig(rd.getParent()),
                                rd.getStartLoc()));
                        } else {
                            locks.push(ThisExpr.make(sig, rd.getStartLoc()));
                        }
                    } else if (rd instanceof ConstructorDecl) {
                        if (RccOptions.get().chl) {
                            locks.push(ThisExpr.make(sig, rd.getStartLoc()));
                        }
                    }
                    ExprVec expressions = getRequiresVec(rd);
                    for (int i = 0; i < expressions.size(); i++) {
                        locks.push(expressions.elementAt(i));
                    }
                    // end rcc-specific code

                    env = checkStmt(env, rd.body);
                } finally {
                    locks.popToMark(); // the finally block is rcc-specific
                }
            }
            break;
        }

        case TagConstants.INITBLOCK: {
            locks.mark();
            InitBlock si = (InitBlock) e;
            PrepTypeDeclaration.getInst().checkModifiers(
                si.modifiers,
                Modifiers.ACC_STATIC,
                si.getStartLoc(),
                "initializer body");
            staticContext = Modifiers.isStatic(si.modifiers);
            Env rootEnv = staticContext ? rootSEnv : rootIEnv;
            Env env = addGhosts(sig, rootEnv);
            if (RccOptions.get().ihl) {
                if (staticContext) {
                    locks.push(ClassLiteral.make(
                        TypeSig.getSig(si.getParent()),
                        si.getStartLoc()));
                } else {
                    locks.push(ThisExpr.make(sig, si.getStartLoc()));
                }
            }
            if (RccOptions.get().ihnl && staticContext) {
                locks.push(LiteralExpr.make(
                    TagConstants.NULLLIT,
                    null,
                    si.getStartLoc()));
            }
            returnType = null;
            canAssignReadOnly = true;
            env = new EnvForEnclosedScope(env);
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

    static public ExprVec getRequiresVec(RoutineDecl rd) {
        ExprVec expressions = (ExprVec) requiresDecoration.get(rd);
        if (expressions == null) {
            FlowInsensitiveChecks a = new FlowInsensitiveChecks();
            inAnnotation = true;
            a.sig = TypeSig.getSig(rd.parent);
            expressions = a.checkRequiresVec(rd);
            inAnnotation = false;
        }
        return expressions;
    }

    // === Extensions to expression and statement checkers ===

    protected Env checkStmt(Env env, Stmt s) {
        if (inAnnotation) { return env; }
        int tag = s.getTag();
        // System.out.println("process stmt: " +
        // TagConstants.toString(s.getTag()));
        switch (tag) {
        case TagConstants.SYNCHRONIZESTMT:
            try {
                locks.mark();
                SynchronizeStmt ss = (SynchronizeStmt) s;
                ss.expr = checkExpr(env, ss.expr, Types.javaLangObject());
                locks.push(ss.expr);
                checkStmt(env, ss.stmt);
            } finally {
                locks.popToMark();
            }
            break;

        case TagConstants.CONSTRUCTORINVOCATION: {
            ConstructorInvocation ci = (ConstructorInvocation) s;
            env = super.checkStmt(env, s);
            if (ci.decl == null) return env; // SNF
            ExprVec expressions = getRequiresVec(ci.decl);
            SubstitutionVec subs = SubstitutionVec.make();
            MultipleSubstitution ms = new MultipleSubstitution(subs);
            checkLocksHeld(
                ms,
                expressions,
                ci.getStartLoc(),
                ci.decl.pmodifiers);
            return env;
        }

        default:
            // new Exception().printStackTrace();
            env = super.checkStmt(env, s);
            break;
        }

        return env;
    }

    protected boolean lockHeld(MultipleSubstitution ms, Expr e) {
        CloneWithSubstitution c = new CloneWithSubstitution(ms);
        // dbg(e);
        e = (Expr) c.clone(e, true);
        // dbg(e);

        // System.out.println (" ---locks " + locks.expressionsToString());
        // System.out.println (" ---expression "+e);

        return locks.contains(e);
    }

    /*
     * DBG protected Expr checkExpr(Env env, Expr x) { if (x != null)
     * System.out.println(TagConstants.toString(x.getTag())); return
     * super.checkExpr(env, x); }
     */

    static public rcc.tc.TypeSig defaultInstantiation(rcc.tc.TypeSig sig) {
        boolean t = inAnnotation;
        inAnnotation = true;
        FormalParaDeclVec fpv = (FormalParaDeclVec) PrepTypeDeclaration.typeParametersDecoration.get(sig);

        ExprVec args = ExprVec.make();
        if (fpv != null) {
            for (int i = 0; i < fpv.size(); i++) {
                FormalParaDecl parameter = fpv.elementAt(i);
                ExprObjectDesignator eod = ExprObjectDesignator.make(
                    parameter.getStartLoc(),
                    ThisExpr.make(sig, parameter.getStartLoc()));
                FieldAccess fa = FieldAccess.make(
                    eod,
                    parameter.id,
                    parameter.getStartLoc());
                args.addElement(fa);
                sig.getEnv(true).resolveType(sig, parameter.type); // TODO:
                // check
                // (rgrig)
                setType(fa, parameter.type);
                fa.decl = (FieldDecl) PrepTypeDeclaration.parameterDeclDecoration.get(parameter);
                setType(eod.expr, sig); // good enough for now. change below to
                // correct sig
            }
        }
        TypeSig s = ((rcc.tc.PrepTypeDeclaration) PrepTypeDeclaration.getInst()).findTypeSignature(
            sig.getEnv(true),
            sig,
            args,
            sig.getTypeDecl().getStartLoc());

        for (int i = 0; i < args.size(); i++) {
            FieldAccess fa = (FieldAccess) args.elementAt(i);
            setType(((ExprObjectDesignator) fa.od).expr, s);
            s.getEnv(true).resolveType(sig, getType(fa)); // TODO: check
            // (rgrig)
        }

        inAnnotation = t;
        return (rcc.tc.TypeSig) s;
    }

    protected void checkLocksHeld(
        MultipleSubstitution ms,
        ExprVec expressions,
        int line,
        ModifierPragmaVec mpv) {
        Expr expr;

        // System.out.println ("---locks " + locks.toString());
        // System.out.println ("---substitutions " + ms.toString());
        // System.out.println ("---expressions " + expressions.toString());

        for (int i = 0; i < expressions.size(); i++) {
            expr = expressions.elementAt(i);
            // dbg(expr);
            if (!lockHeld(ms, expr)) {
                CloneWithSubstitution c = new CloneWithSubstitution(ms);
                int declLoc = getLocInPragmas(expr, mpv);
                // dbg(expr);
                expr = (Expr) c.clone(expr, true);
                // dbg(expr);
                ErrorMsg.print(sig, "Race", line, "Lock '"
                    + PrettyPrint.inst.toString(expr) + "' may not be held."
                    + "  Locks currently held are '" + locks + "'.", declLoc);
            }
        }
    }

    // version for array access
    protected void checkLocksHeld(
        MultipleSubstitution ms,
        ExprVec expressions,
        int line) {
        Expr expr;

        // System.out.println ("---locks " + locks.toString());
        // System.out.println ("---substitutions " + ms.toString());
        // System.out.println ("---expressions " + expressions.toString());

        for (int i = 0; i < expressions.size(); i++) {
            expr = expressions.elementAt(i);
            // dbg(expr);
            if (!lockHeld(ms, expr)) {
                CloneWithSubstitution c = new CloneWithSubstitution(ms);
                expr = (Expr) c.clone(expr, true);
                int declLoc = expr.getStartLoc(); // FIX TO PRINT RIGHT LOC
                ErrorMsg.print(sig, "Race", line, "Lock '"
                    + PrettyPrint.inst.toString(expr) + "' may not be held."
                    + "  Locks currently held are '" + locks + "'.", declLoc);
            }
        }
    }

    // DBG: private Hashtable dbgh = new Hashtable();

    // TODO: Commment this!
    protected Type modifyEscapingType(Env env, SubstitutionVec s, Type type) {
        MultipleSubstitution ms = new MultipleSubstitution(s);
        CloneWithSubstitution c = new CloneWithSubstitution(ms);

        // dbg(type);
        type = (Type) c.clone(type, true);

        if (type instanceof ArrayType) {
            // Recurse for array case. This wastes some work, but the
            // alternative is to make a new clone class.
            /*
             * ((ArrayType) type).elemType = modifyEscapingType(env, s,
             * ((ArrayType) type).elemType);
             */
            // Do nothing.
        }

        if (type instanceof TypeName) {
            type = TypeSig.getSig((TypeName) type);
        }

        if (type instanceof rcc.tc.TypeSig) {
            rcc.tc.TypeSig tsig = (rcc.tc.TypeSig) type;
            if (tsig.generic != null) {
                CloneForInstantiation ci = new CloneForInstantiation(ms);
                ExprVec args = ci.clone(tsig.expressions, true);
                rcc.tc.PrepTypeDeclaration preparer = (rcc.tc.PrepTypeDeclaration) PrepTypeDeclaration.getInst();
                type = preparer.findTypeSignature(
                    env,
                    tsig.generic,
                    args,
                    Location.NULL);
            }
        }

        // if (type != null) dbg(type);
        return type;
    }

    // TODO: Comment this!
    protected void modifyEscapingExpr(Env env, SubstitutionVec s, VarInit e) {
        setType(e, modifyEscapingType(env, s, getType(e)));
    }

    // === Begin: Custom typechecking ===

    /*
     * NOTE Given the following inner class. class A { public class B { public X
     * x; //# guarded_by A.this } } The enclosing class is available only within
     * B's scope (by using the syntax [A.this]). This means that within B's
     * scope we can verify if a [synchronize(A.this)] statement exists or not.
     * However, any attempt to refer to x from other places (including from
     * class A) cannot be verified because we have no way of referring to B's
     * enclosing class and hence it is not possible for a _clearly_ good (at
     * compile time) synchronize statement to exist. Therefore, all such uses
     * should be flagged as errors.
     */
    // TODO: How to handle other nested classes (e.g., static nested)?
    // TODO: Clarify how access modifiers impact the reasoning above.
    /**
     * Typechecks field access. Unlike the overriden method it also takes into
     * account ghost fields.
     */
    // @ ensures getTypeOrNull(\result) != null;
    protected FieldAccess checkFieldAccessExpr(
    /* @ non_null */Env env,
    /* @ non_null */FieldAccess fa) {
        fa = super.checkFieldAccessExpr(env, fa);

        // If there was no error in the standard typecheck and we
        // are in code then we do some additional processing.
        if (fa.decl != null && !inAnnotation) {
            // If the access is [x.y] and field [y] is supposed to be
            // guarded by [this] then it is in fact supposed to be guarded
            // by [x]. That is why we substitute [x] for [this] in
            // the list of locks associated with [y].
            SubstitutionVec s = SubstitutionVec.make();
            if (!Modifiers.isStatic(fa.decl.modifiers)
                && fa.od.getTag() == TagConstants.EXPROBJECTDESIGNATOR
                && fa.decl.parent != null) {
                // NOTE: The first parameter of [ThisExpr.make] used to be
                // [TypeSig.getSig(fa.decl.parent)]. This means we replaced
                // [CLASS.this] with the object. But now we don't process
                // [this] into [CLASS.this].

                // TODO: The user might write by hand [CLASS.this] thou. This is
                // very unlikely so it's not handled. Correct treatment should
                // take into account inheritance.
                Expr object = ((ExprObjectDesignator) fa.od).expr;
                // System.out.print("this -> ");
                // dbg(object);
                s.addElement(new Substitution(ThisExpr.make(
                    null,
                    fa.od.getStartLoc()), object));
            }
            modifyEscapingExpr(env, s, fa);
            // dbg(fa);
            ExprVec expressions = getGuardedVec(fa.decl);
            // dbg(expressions);
            MultipleSubstitution ms = new MultipleSubstitution(s);

            checkLocksHeld(
                ms,
                expressions,
                fa.getStartLoc(),
                fa.decl.pmodifiers);
        }

        return fa;
    }

    /**
     * Prepare substitutions for invocation of methods with ghost variables.
     */
    // TODO: Annotate this!
    protected MethodInvocation checkMethodInvocationExpr(
    /* @ non_null */Env env,
    /* @ non_null */MethodInvocation mi) {
        mi = super.checkMethodInvocationExpr(env, mi);
        if (mi == null) return mi; // SNF
        if (!inAnnotation) {
            if (mi.decl == null) return mi;
            ExprVec expressions = getRequiresVec(mi.decl);
            boolean staticContext = Modifiers.isStatic(mi.decl.modifiers);
            SubstitutionVec s = SubstitutionVec.make();
            if (!staticContext
                && mi.od.getTag() == TagConstants.EXPROBJECTDESIGNATOR) {
                s.addElement(new Substitution(ThisExpr.make(
                    TypeSig.getSig(mi.decl.parent),
                    mi.od.getStartLoc()), ((ExprObjectDesignator) mi.od).expr));
            }

            for (int i = 0; i < mi.args.size(); i++) {
                FormalParaDecl parameter = mi.decl.args.elementAt(i);
                Expr expr = mi.args.elementAt(i);
                FieldAccess fa = FieldAccess.make(
                    ExprObjectDesignator.make(
                        parameter.getStartLoc(),
                        ThisExpr.make(
                            TypeSig.getSig(mi.decl.parent),
                            parameter.getStartLoc())),
                    parameter.id,
                    parameter.getStartLoc());
                s.addElement(new Substitution(fa, expr));
                s.addElement(new Substitution(VariableAccess.make(
                    parameter.id,
                    parameter.getStartLoc(),
                    parameter), expr));
            }
            modifyEscapingExpr(env, s, mi);

            MultipleSubstitution ms = new MultipleSubstitution(s);
            checkLocksHeld(
                ms,
                expressions,
                mi.getStartLoc(),
                mi.decl.pmodifiers);
        }
        return mi;
    }

    /**
     * @param env The environment in which to check the new expression.
     * @return The environment after the new expression.
     */
    // TODO: Annotate this!
    protected NewInstanceExpr checkNewInstanceExpr(
    /* @ non_null */Env env,
    /* @ non_null */NewInstanceExpr ne) {
        ne = super.checkNewInstanceExpr(env, ne);
        if (ne == null) return ne; // SNF
        if (!inAnnotation) {
            if (ne.decl == null) return ne;
            ExprVec expressions = getRequiresVec(ne.decl);
            SubstitutionVec s = SubstitutionVec.make();

            for (int i = 0; i < ne.args.size(); i++) {
                FormalParaDecl parameter = ne.decl.args.elementAt(i);
                Expr expr = ne.args.elementAt(i);
                FieldAccess fa = FieldAccess.make(
                    ExprObjectDesignator.make(
                        parameter.getStartLoc(),
                        ThisExpr.make(
                            TypeSig.getSig(ne.decl.parent),
                            parameter.getStartLoc())),
                    parameter.id,
                    parameter.getStartLoc());
                s.addElement(new Substitution(fa, expr));

                s.addElement(new Substitution(VariableAccess.make(
                    parameter.id,
                    parameter.getStartLoc(),
                    parameter), expr));
            }

            modifyEscapingExpr(env, s, ne);
            MultipleSubstitution ms = new MultipleSubstitution(s);
            checkLocksHeld(
                ms,
                expressions,
                ne.getStartLoc(),
                ne.decl.pmodifiers);
        }
        return ne;
    }

    /**
     * Check that the locks on the element of the array are held.
     */
    // @ ensures getTypeOrNull(\result) != null;
    protected ArrayRefExpr checkArrayRefExpr(
    /* @ non_null */Env env,
    /* @ non_null */ArrayRefExpr r) {
        r = super.checkArrayRefExpr(env, r);

        Type t = getType(r.array);
        // dbg(t);
        if (!inAnnotation && t instanceof ArrayType) {
            ExprVec exps = getElemGuardedVec(t, env);
            // dbg(t); dbg(exps);
            MultipleSubstitution ms = new MultipleSubstitution();
            checkLocksHeld(ms, exps, r.locOpenBracket);
        }

        return r;
    }

    // === Pragma checkers : begin ===
    /*
     * These are responsible for transforming pragmas into decorations. (AST
     * nodes representing pragmas are morphed into `fields' of the context AST
     * node using the [ASTDecoration] mechanism.) In the process we also check
     * `syntactic' properties of pragmas; for example, a `requires' annotation
     * makes sense only on a method. Note that there are two types of pragmas:
     * the normal ones and those associated with types, which are named `type
     * pragmas'.
     */

    /**
     * Dispatch to the pragma handlers for classes, interfaces, methods,
     * monstructors, and fields.
     */
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
        return env;
    }

    /** Dispatch to <code>getElemGuardedVec</code>. */
    public Env checkTypeModifierPragmaVec(
        TypeModifierPragmaVec mod,
        ASTNode a,
        Env env) {
        getElemGuardedVec((Type) a, env);
        return env;
    }

    protected void checkTypeDeclElemPragma(TypeDeclElemPragma e) {
        Assert.notFalse(
            e.getTag() == TagConstants.GHOSTDECLPRAGMA,
            "Unexpected tag " + e.getTag());
    }

    /**
     * Transforms <tt>elems_guarded_by</tt> type pragmas into an AST
     * decoration. Reports an error if it appears in something else other than
     * an array type.
     */
    // @ ensures !inAnnotation;
    protected Env checkTypeModifierPragma(
        TypeModifierPragma p,
        ASTNode ctxt,
        Env env) {
        inAnnotation = true;
        int tag = p.getTag();
        switch (tag) {
        case TagConstants.ARRAYGUARDMODIFIERPRAGMA: {
            ArrayGuardModifierPragma rp = (ArrayGuardModifierPragma) p;
            checkLockExprVec(env, rp.expressions, rp.getStartLoc());
            // dbg(rp.expressions);
            if (ctxt.getTag() != TagConstants.ARRAYTYPE) {
                ErrorMsg.print(
                    sig,
                    "Modifiers",
                    ctxt.getStartLoc(),
                    "only array declarations may contain this type of annotation.",
                    Location.NULL);
            }
            // log.info("Transforming elems_guarded_by into a decoration.");
            ExprVec g = (ExprVec) elemGuardDecoration.get(ctxt);
            for (int i = 0; i < rp.expressions.size(); i++) {
                g.addElement(rp.expressions.elementAt(i));
            }
            // dbg(g);
            break;
        }
        case TagConstants.GENERICARGUMENTPRAGMA:
            // handled in Prep stage
            break;
        default:
            // @ unreachable;
            Assert.fail("Unexpected tag " + tag);
        }
        inAnnotation = false;
        return env;
    }

    /**
     * Transforms a modifier pragma into the appropriate AST annotation, using
     * the <code>ASTDecoration</code> mechanism. It also performs some
     * "syntactic" checks on the existing pragmas.
     */
    protected Env checkModifierPragma(ModifierPragma p, ASTNode ctxt, Env env) {

        inAnnotation = true; // Must be reset before we exit!
        int tag = p.getTag();
        switch (tag) {
        case TagConstants.READONLYMODIFIERPRAGMA:
            // TODO: Comment this!
            break;

        case TagConstants.REQUIRESMODIFIERPRAGMA: {
            RequiresModifierPragma rp = (RequiresModifierPragma) p;
            checkLockExprVec(env, rp.expressions, rp.getStartLoc());
            if (ctxt.getTag() != TagConstants.METHODDECL
                && ctxt.getTag() != TagConstants.CONSTRUCTORDECL) {
                ErrorMsg.print(
                    sig,
                    "Modifiers",
                    ctxt.getStartLoc(),
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
            if (ctxt.getTag() == TagConstants.CLASSDECL) break; // already done
            GuardedByModifierPragma rp = (GuardedByModifierPragma) p;
            checkLockExprVec(env, rp.expressions, rp.getStartLoc());
            if (ctxt.getTag() != TagConstants.FIELDDECL
                && ctxt.getTag() != TagConstants.CLASSDECL) {
                ErrorMsg.print(
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
                ErrorMsg.print(
                    sig,
                    "ThreadLocal",
                    ctxt.getStartLoc(),
                    "thread_local/thread_shared only allowed on classes and interfaces.",
                    Location.NULL);
                break;
            }
            if (threadLocalDecoration.get(ctxt) != null) {
                ErrorMsg.print(
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
            if (RccOptions.get().pun) {
                for (int i = 0; i < cs.expressions.size(); i++) {
                    Expr e = cs.expressions.elementAt(i);
                    if (locks.contains(e)) {
                        ErrorMsg.print(sig, "Race", e.getStartLoc(), "lock '"
                            + PrettyPrint.inst.toString(e)
                            + "' is already held", Location.NULL);
                    }
                }
            }
            if (!RccOptions.get().noho) {
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
        env = new EnvForEnclosedScope(env);
        for (int j = 0; j < rd.args.size(); j++) {
            FormalParaDecl formal = rd.args.elementAt(j);
            PrepTypeDeclaration.getInst().checkModifiers(
                formal.modifiers,
                Modifiers.ACC_FINAL,
                formal.getStartLoc(),
                "formal parameter");
            checkModifierPragmaVec(formal.pmodifiers, formal, env);
            env = new EnvForLocals(env, formal);
        }

        super.checkModifierPragmaVec(rd.pmodifiers, rd, env);

        // check overridden expr ved
        if (rd instanceof MethodDecl) {
            MethodDecl md = (MethodDecl) rd;
            Set methods = javafe.tc.PrepTypeDeclaration.getInst().getOverrides(
                md);
            Enumeration e = methods.elements();
            while (e.hasMoreElements()) {
                MethodDecl m = (MethodDecl) e.nextElement();
                ExprVec superExpressions = getRequiresVec(m);
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

    /**
     * @param exps A vector of expressions.
     * @return Whether there are two distinct elements in exps which are equal
     *         according to <code>EqualsASTNoDecl</code>.
     */
    protected boolean checkDuplicateExpressions(ExprVec exps) {
        EqualsASTNoDecl eq = new EqualsASTNoDecl();

        for (int i = 0; i < exps.size(); ++i) {
            Expr ei = exps.elementAt(i);
            for (int j = i + 1; j < exps.size(); ++j) {
                Expr ej = exps.elementAt(j);
                if (eq.equals(ei, ej)) return true;
            }
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

        if (RccOptions.get().prg) {
            if (checkDuplicateExpressions(g)) {
                ErrorMsg.print(sig, "Modifiers", fd.getStartLoc(), "field '"
                    + fd.id
                    + "' has redundant guard annotations.  Guards are: '"
                    + PrettyPrint.inst.toString(g) + "'", Location.NULL);
            }
        }

        return g;
    }

    // TODO: Comment this!
    // for type modifiers, we will always be in the current environment.
    public ExprVec checkElemGuardedVec(Type t, Env env) {
        ExprVec g = ExprVec.make();
        elemGuardDecoration.set(t, g);
        super.checkTypeModifierPragmaVec(t.tmodifiers, t, env);
        // dbg(g);

        if (RccOptions.get().prg) {
            if (checkDuplicateExpressions(g)) {
                ErrorMsg.print(
                    sig,
                    "Modifiers",
                    t.getStartLoc(),
                    "array type has redundant guard annotations.  Guards are: '"
                        + PrettyPrint.inst.toString(g) + "'",
                    Location.NULL);
            }
        }

        return g;
    }

    static public ExprVec getGuardedVec(FieldDecl fd) {
        ExprVec expressions = (ExprVec) guardDecoration.get(fd);
        if (expressions == null) {
            FlowInsensitiveChecks a = new FlowInsensitiveChecks();
            inAnnotation = true;
            if (fd.parent != null) {
                a.sig = TypeSig.getSig(fd.parent);
                expressions = a.checkGuardedVec(fd);
            } else {
                // length field of array
                Assert.notFalse(fd == Types.lengthFieldDecl);
                guardDecoration.set(fd, expressions = ExprVec.make());
            }
            inAnnotation = false;
        }
        return expressions;
    }

    // TODO: Comment this!
    static public ExprVec getElemGuardedVec(Type t, Env env) {
        ExprVec expressions = (ExprVec) elemGuardDecoration.get(t);
        // dbg(t); dbg(expressions);
        if (env == null) {
            env = (Env) Env.typeEnv.get(t);
        }
        if (expressions == null) {
            FlowInsensitiveChecks a = new FlowInsensitiveChecks();
            inAnnotation = true; // inAnnotation is static
            a.sig = env.getEnclosingClass(); // SNF
            a.rootSEnv = a.makeEnvForTypeSig(a.sig, true);
            a.rootIEnv = a.makeEnvForTypeSig(a.sig, false);
            // expressions = a.checkElemGuardedVec(t,a.rootIEnv);
            // System.out.println(" " + env.isStaticContext()+ env +
            // env.getEnclosingClass());
            expressions = a.checkElemGuardedVec(t, env);
            // dbg(expressions);
            inAnnotation = false;
        }
        // dbg(locks);
        return expressions;
    }

    // === Pragma checkers : end ===

    protected Expr checkFinalExpr(Env env, Expr expr, int assocLoc) {
        Assert.notFalse(expr != null);
        Expr checkExpr = checkExpr(env, expr, Types.javaLangObject());
        if (!isFinalExpr(env, checkExpr)) {
            ErrorMsg.print(
                sig,
                "ConstantLocks",
                expr.getStartLoc(),
                "",
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

    // === Utility routines : begin ===

    /**
     * * Copy the Type associated with an expression by the typechecking * pass
     * to another Expr. This is used by Substitute to ensure it * returns an
     * Expr of the same Type.
     */
    public static void copyType(VarInit from, VarInit to) {
        Type t = getTypeOrNull(from);
        if (t != null) setType(to, t);
    }

    /**
     * Return a set of *all* the methods a given method (transitively)
     * overrides.
     */
    // @ requires md!=null
    // @ ensures RES!=null
    public static Set getAllOverrides(MethodDecl md) {
        Set direct = javafe.tc.PrepTypeDeclaration.getInst().getOverrides(md);
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
        if (!(rd instanceof MethodDecl)) { return null; }
        MethodDecl md = (MethodDecl) rd;
        MethodDecl override = null;
        Set direct = javafe.tc.PrepTypeDeclaration.getInst().getOverrides(md);
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
            if (!isFinalObjectDesignator(env, fa.od)) { return false;

            }
            try {
                FieldDecl fd = Types.lookupField(getObjectDesignatorType(
                    env,
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
            if (t instanceof TypeName) t = TypeSig.getSig((TypeName) t);
            Assert.notFalse(t instanceof TypeSig); // @ nowarn Pre
            return (TypeSig) t;
        }

        case TagConstants.SUPEROBJECTDESIGNATOR: {
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
                if (rmp.expressions.contains(expr)) { return rmp.getStartLoc(); }
            } else if (mp instanceof GuardedByModifierPragma) {
                GuardedByModifierPragma gmp = (GuardedByModifierPragma) mp;
                if (gmp.expressions.contains(expr)) { return gmp.getStartLoc(); }
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
            inAnnotation = true; // TODO: shouldn't this be reset at method
            // exit?
            a.rootSEnv = a.makeEnvForTypeSig(a.sig, true); // @ nowarn
            a.rootIEnv = a.makeEnvForTypeSig(a.sig, false); // @ nowarn

            // b = a.checkLocalThreadStatus(d,a.sig.getEnclosingEnv());
            b = a.checkLocalThreadStatus(d, a.rootIEnv);
        }
        return b.booleanValue();
    }

    public Boolean checkLocalThreadStatus(TypeDecl d, Env env) {
        super.checkModifierPragmaVec(d.pmodifiers, d, env);
        Boolean b = ((Boolean) threadLocalDecoration.get(d));

        boolean onCommandLine = rcc.Main.inst != null
            && rcc.Main.inst.commandLineFiles.contains(TypeSig.getSig(d).getCompilationUnit());

        /* to shortcircuit inference: */
        if (b != null) {
            if (b.booleanValue()) {
                checkThreadLocal(env, d);
            } else {
                checkThreadShared(env, d);
            }
        } else if (RccOptions.get().dts && onCommandLine) {
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
                ErrorMsg.print(
                    sig,
                    "ThreadLocal",
                    d.getStartLoc(),
                    "cannot be local or shared",
                    Location.NULL);
                threadLocalDecoration.set(d, new Boolean(true));
            }
        }

        Info.out("[infering that "
            + TypeSig.getSig(d).simpleName
            + " is "
            + (((Boolean) threadLocalDecoration.get(d)).booleanValue() ? "thread local"
                : "thread shared") + "]");

        commonThreadLocal(env, d);

        return ((Boolean) threadLocalDecoration.get(d));
    }

    private boolean guardPragmaExists(ModifierPragmaVec m) {
        if (m == null) return false;
        for (int i = 0; i < m.size(); i++) {
            if (m.elementAt(i) instanceof GuardedByModifierPragma) { return true; }
        }
        return false;
    }

    private ReadOnlyModifierPragma readOnlyPragma(ModifierPragmaVec m) {
        if (m == null) return null;
        for (int i = 0; i < m.size(); i++) {
            if (m.elementAt(i) instanceof ReadOnlyModifierPragma) { return (ReadOnlyModifierPragma) m.elementAt(i); }
        }
        return null;
    }

    private boolean requiresPragmaExists(ModifierPragmaVec m) {
        if (m == null) return false;
        for (int i = 0; i < m.size(); i++) {
            if (m.elementAt(i) instanceof RequiresModifierPragma) { return true; }
        }
        return false;
    }

    private boolean elementGuardPragmaExists(Type a) {
        if (!(a instanceof ArrayType)) { return false; }
        TypeModifierPragmaVec m = ((ArrayType) a).tmodifiers;
        if (m == null) return false;
        for (int i = 0; i < m.size(); i++) {
            if (m.elementAt(i) instanceof ArrayGuardModifierPragma) { return true; }
        }
        return false;
    }

    private boolean arrayGuarded(Type a) {
        if (!(a instanceof ArrayType)) { return true; }
        TypeModifierPragmaVec m = ((ArrayType) a).tmodifiers;
        if (m == null) return false;
        for (int i = 0; i < m.size(); i++) {
            if (m.elementAt(i) instanceof ArrayGuardModifierPragma) { return arrayGuarded(((ArrayType) a).elemType); }
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
                            ErrorMsg.print(
                                sig,
                                "ThreadLocal",
                                fd.getStartLoc(),
                                "the class '"
                                    + TypeSig.getSig(d).getExternalName()
                                    + "' must be thread shared because field '"
                                    + TypeSig.getSig(d).getExternalName() + "."
                                    + fd.id + "' is static",
                                threadLocalAnnotationLoc(decl));
                        }
                    }
                    if (!Modifiers.isFinal(fd.modifiers)
                        && readOnlyPragma(fd.pmodifiers) == null) {
                        if (!guardPragmaExists(fd.pmodifiers)) {
                            ErrorMsg.print(
                                sig,
                                "StaticField",
                                fd.getStartLoc(),
                                "field '"
                                    + TypeSig.getSig(d).getExternalName()
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
        if (mpv == null) return d.getStartLoc();
        for (int i = 0; i < mpv.size(); i++) {
            ModifierPragma p = mpv.elementAt(i);
            if (p.getTag() == TagConstants.THREADLOCALSTATUSPRAGMA) { return p.getStartLoc(); }
        }
        return d.getStartLoc();
    }

    // TODO: substitute param names from super class for alpha renaming.
    public void checkThreadLocal(Env env, TypeDecl d) {
        TypeDeclElem elem;

        if (Types.isSubclassOf(TypeSig.getSig(d), Types.getJavaLang("Thread"))) {
            ErrorMsg.print(
                sig,
                "ThreadLocal",
                d.getStartLoc(),
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
                Set methods = javafe.tc.PrepTypeDeclaration.getInst().getOverrides(
                    md);

                Enumeration e = methods.elements();
                while (e.hasMoreElements()) {

                    MethodDecl superDecl = (MethodDecl) e.nextElement();
                    if (!getLocalThreadStatus(superDecl.parent, env)) {
                        ErrorMsg.print(sig, "Override", md.getStartLoc(), "'"
                            + md.id.toString() + "'", superDecl.getStartLoc());
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

        if (d instanceof InterfaceDecl) { return false; }

        if (d == Types.getJavaLang("Thread").getTypeDecl()) { return false; }

        for (int i = 0; i < d.elems.size(); i++) {
            elem = d.elems.elementAt(i);
            switch (elem.getTag()) {
            case TagConstants.FIELDDECL: {
                FieldDecl fd = (FieldDecl) elem;
                if (guardPragmaExists(fd.pmodifiers)
                    || elementGuardPragmaExists(((FieldDecl) elem).type)) { return false; }
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
            TypeDecl parent = env.resolveTypeName(
                null,
                ((ClassDecl) d).superClass) // TODO: check
                .getTypeDecl();
            if (parent != null && getLocalThreadStatus(parent, env)) {
                ErrorMsg.print(
                    sig,
                    "ThreadLocal",
                    d.getStartLoc(),
                    "super class '" + TypeSig.getSig(parent).getExternalName()
                        + "' of thread shared class '"
                        + TypeSig.getSig(d).getExternalName()
                        + "' must be thread shared",
                    parent.getStartLoc());
            }
        }

        for (int i = 0; i < d.superInterfaces.size(); i++) {
            TypeDecl p = env.resolveTypeName(
                null,
                d.superInterfaces.elementAt(i)) // TODO: check
                .getTypeDecl();
            if (getLocalThreadStatus(p, env)) {
                ErrorMsg.print(
                    sig,
                    "ThreadLocal",
                    d.getStartLoc(),
                    "thread shared class "
                        + TypeSig.getSig(d).getExternalName()
                        + " can not implement thread local interface " + p.id,
                    threadLocalAnnotationLoc(p));
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
                        if (RccOptions.get().agt) {
                            if (!unsharedFieldSeen) {
                                Info.out("[assuming the unguarded fields of "
                                    + sig + " are guarded by this/" + sig
                                    + ".class]");
                                unsharedFieldSeen = true;
                            }
                            ExprVec expressions = ExprVec.make();
                            if (Modifiers.isStatic(fd.modifiers)) {
                                expressions.addElement(ClassLiteral.make(
                                    sig,
                                    fd.getStartLoc()));
                            } else {
                                expressions.addElement(ThisExpr.make(
                                    sig,
                                    fd.getStartLoc()));
                            }
                            if (fd.pmodifiers == null) {
                                fd.pmodifiers = ModifierPragmaVec.make();
                            }
                            fd.pmodifiers.addElement(GuardedByModifierPragma.make(
                                expressions,
                                fd.getStartLoc()));
                        } else {
                            if (!Modifiers.isStatic(fd.modifiers)) {
                                ErrorMsg.print(
                                    sig,
                                    "SharedField",
                                    fd.getStartLoc(),
                                    "field '"
                                        + TypeSig.getSig(d).getExternalName()
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
                    if (RccOptions.get().agt) {
                        if (!unsharedFieldSeen) {
                            Info.out("[assuming the unguarded array elements of "
                                + sig
                                + " are guarded by this/"
                                + sig
                                + ".class]");
                            unsharedFieldSeen = true;
                        }
                        ExprVec expressions = ExprVec.make();
                        if (Modifiers.isStatic(fd.modifiers)) {
                            expressions.addElement(ClassLiteral.make(
                                sig,
                                fd.getStartLoc()));
                        } else {
                            expressions.addElement(ThisExpr.make(
                                sig,
                                fd.getStartLoc()));
                        }
                        if (fd.type.tmodifiers == null) {
                            fd.type.tmodifiers = TypeModifierPragmaVec.make();
                        }
                        fd.type.tmodifiers.addElement(ArrayGuardModifierPragma.make(
                            expressions,
                            fd.getStartLoc()));
                    } else {
                        ErrorMsg.print(
                            sig,
                            "SharedArray",
                            fd.getStartLoc(),
                            "elements of array '"
                                + TypeSig.getSig(d).getExternalName() + "."
                                + fd.id
                                + "' must be guarded in a thread shared class",
                            Location.NULL);
                    }
                }

                javafe.tc.TypeSig type = null;
                if (fd.type instanceof TypeName) {
                    type = TypeSig.getSig((TypeName) fd.type);
                    if (type == null) {
                        ErrorMsg.print(
                            sig,
                            "ThreadLocal",
                            fd.getStartLoc(),
                            "cannot find class " + fd.type,
                            Location.NULL);
                        break;
                    }
                }
                if (fd.type instanceof javafe.tc.TypeSig) {
                    type = (javafe.tc.TypeSig) fd.type;
                }
                if (type != null) { // we have a typesig as the type
                    TypeDecl decl = type.getTypeDecl();
                    if (getLocalThreadStatus(decl, env)) {
                        ErrorMsg.print(
                            sig,
                            type,
                            "ThreadLocal",
                            fd.getStartLoc(),
                            "the class '" + type
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
            || Types.isSubclassOf(
                TypeSig.getSig(d),
                Types.getJavaLang("Thread"))) { return true; }

        if (d == Types.getJavaLang("Object").getTypeDecl()) { return true; }

        if (d instanceof InterfaceDecl) { return true; }

        for (int i = 0; i < d.elems.size(); i++) {
            elem = d.elems.elementAt(i);
            switch (elem.getTag()) {
            case TagConstants.FIELDDECL:
                FieldDecl fd = (FieldDecl) elem;
                if (guardPragmaExists(fd.pmodifiers)) { return true; }
                break;

            case TagConstants.METHODDECL:
                MethodDecl md = (MethodDecl) elem;
                if (Modifiers.isSynchronized(md.modifiers)
                    || requiresPragmaExists(md.pmodifiers)) { return true; }
                break;
            }
        }
        return false;
    }

    /**
     * Verifies that readonly variables are not written to when
     * <code>canAssignReadOnly</code>. Other parts of this class are
     * responsible for resetting <code>canAssignReadOnly</code> when we are in
     * in a lvalue position.
     */
    protected Expr checkDesignator(Env env, Expr e) {
        e = super.checkDesignator(env, e);

        if (!canAssignReadOnly) {
            // check readonly
            ReadOnlyModifierPragma romp = null;
            // System.out.println("checkDesignator " + e);
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
                        env,
                        fa.od), fa.id, sig);
                    romp = readOnlyPragma(fd.pmodifiers);
                } catch (LookupException le) {
                    // The field might be duplicated.
                    Assert.notFalse(ErrorSet.errors != 0);
                }
                break;
            }
            }
            if (romp != null) {
                ErrorMsg.print(
                    sig,
                    "ReadOnly",
                    e.getStartLoc(),
                    "Assigning a variable declared as readonly",
                    romp.getStartLoc());
            }
        }

        return e;
    }

    // === Utility routines : end ===

    // === Testing and debugging : begin ===
    /*
     * static private Logger log = Logger.getLogger("Rcc flow checks"); private
     * static void dbg(ExprVec exprs) {
     * System.out.println(PrettyPrint.inst.toString(exprs)); } private static
     * void dbg(Expr expr) {
     * System.out.println(PrettyPrint.inst.toString(expr)); } private static
     * void dbg(Type type) {
     * System.out.println(PrettyPrint.inst.toString(type)); }
     */
    public static void main(String[] args) {
    // TODO: Implement this!
    }

    // === Testing and debugging : end ===

}
