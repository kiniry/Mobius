/* Copyright 2000, 2001, Compaq Computer Corporation */

package rcc.tc;

import java.util.Enumeration;
import java.util.Hashtable;

import javafe.ast.ASTDecoration;
import javafe.ast.ASTNode;
import javafe.ast.AmbiguousVariableAccess;
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
import javafe.ast.LocalVarDecl;
import javafe.ast.MethodDecl;
import javafe.ast.MethodInvocation;
import javafe.ast.ModifierPragma;
import javafe.ast.ModifierPragmaVec;
import javafe.ast.Modifiers;
import javafe.ast.NewInstanceExpr;
import javafe.ast.ObjectDesignator;
import javafe.ast.PrettyPrint;
import javafe.ast.ReturnStmt;
import javafe.ast.RoutineDecl;
import javafe.ast.Stmt;
import javafe.ast.StmtPragma;
import javafe.ast.SynchronizeStmt;
import javafe.ast.ThisExpr;
import javafe.ast.Type;
import javafe.ast.TypeDecl;
import javafe.ast.TypeDeclElem;
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
import javafe.util.Assert;
import javafe.util.ErrorSet;
import javafe.util.Info;
import javafe.util.Location;
import javafe.util.Set;
import rcc.Dbg;
import rcc.RccOptions;
import rcc.ast.ArrayGuardModifierPragma;
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

/** 
 * NOTE routine = method or constructor
 * 
 * This class is responsible for typechecking the bodies (of methods,
 * constructors, and static blocks). 
 * 
 * TODO rewrite the whole thing
 * TODO don't forget that we drop generic methods
 * 
 * TODO I removed the override of checkTypeDeclaration which
 *      - set an empty guard decl per class
 *      - and checked class modifiers before looking at members
 *      Some assumptions are broken!
 *      
 * TODO The check whether the correct locks are held should be moved into
 *      one method used by checkFieldAccessExpr, checkMethodInvocationExpr,
 *      checkNewInstanceExpr, and maybe others. the only part that is different
 *      is getting the required locks (it is a diffrent annotation on a
 *      differn AST node)
 * 
 * The responsabilities of this class include:
 *  - keep track of the held locks;
 *  - verify that on field access, method invocation, and object creation
 *    the proper locks are held;
 *  - transform most annotations into AST decoration (the exception is
 *    the annotation for generic arguments, which is needed by
 *    PrepTypeDeclaration)
 * 
 * We override the following methods to take keep track of the held locks:
 *  - checkStmtPragma (the `holds' statement)
 * 
 * We override the following to test if the proper locks are held:
 *  - checkArrayRefExpr
 *  - checkFieldAccessExpr
 *  - checkMethodInvocationExpr
 *  - checkNewInstanceExpr
 *  
 * We override the following to check that we don't assign to read-only 
 * variables: (TODO why include locals? why not just fields?) 
 *  - checkDesignator
 *  
 * We override the following and either update the lockset or check the
 * lockset depending on the tag.
 *  - checkStmt (syncronize or constructor invocation)
 *  - checkTypeDeclElem (needs to be rewritten---too complicated)
 * 
 * We override the following to check that annotations appear in the right
 * places and to transform them in AST decorations, which we use later.
 *  - checkModifierPragma 
 *  - checkModifierPragmaVec 
 *    (dispatch to either checkModifierPragma or others depending on annotation)
 *  - checkTypeModifierPragma
 * 
 * We override the following to typecheck expressions used as locks.
 * (NOTE they should be final Object and either ThisExpr or FieldAccess.)
 *  - checkTypeModifierPragmaVec
 * 
 * @see PrepTypeDeclaration, TypeSig, GhostEnv
 * 
 */
public class FlowInsensitiveChecks extends javafe.tc.FlowInsensitiveChecks {

    /** The locks we currently hold. */
    private static LockStack locks = new LockStack();

    /** Used to check AST equality. */
    private static EqualsAST equality = new EqualsAST();

    // === Setup for ghost variables ===
    
    /** 
     * Whether we are or not in an annotation. This field is
     * public because it is also set from <code>PrepTypeDeclaration</code>.
     */
    public static boolean inAnnotation = false;
    
    // The following decorations are accessed by CloneAST

    /** AST decoration for "guarded_by" pragmas. */
    public static final ASTDecoration guardDecoration = new ASTDecoration(
        "guard");

    /** AST decoration for "requires" pragmas. */
    public static final ASTDecoration requiresDecoration = new ASTDecoration(
        "requires");

    /** AST decoration for "elem_guarded_by" pragmas. */
    public static final ASTDecoration elemGuardDecoration = new ASTDecoration(
        "element guard");

    /** AST decoration for "ThreadLocal" pragmas. */
    public static final ASTDecoration threadLocalDecoration = new ASTDecoration(
        "local status");

    // For readonly modifier checking
    /*
     * This variable is true iff we are in a lvalue position. Its name is
     * quite misleading. TODO change the name.
     */
    private boolean canAssignReadOnly;

    /** Initialize a typechecker. */
    public FlowInsensitiveChecks() {
        Dbg.o("creating new typechecker");
        useUniverses = false;
        inst = this;
    }

    /**
     * Initialize a typechecker in a certain environment.
     * 
     * TODO who calls this?
     * 
     * @param sig The type signature in which to typecheck.
     * @param env The current typing environment.
     */
    public FlowInsensitiveChecks(TypeSig sig, EnvForTypeSig env) {
        Dbg.o("creating new typechecker");
        this.sig = sig;

        TypeSig ts = sig;
        if (env != null) {
            ts = (TypeSig)env.getEnclosingClass();
        }
        rootSEnv = makeEnvForTypeSig(ts, true);
        rootIEnv = makeEnvForTypeSig(ts, false);
        
        useUniverses = false;
        inst = this;
    }

    // === Extensions to type declaration member checkers ===
    
    /**
     * Make sure we also check the field initializer, while making
     * sure we consider the proper locks are held. Also check
     * ghost arguments.
     */
    protected void extraCheckFieldDecl(FieldDecl fd) {
        if (fd.init == null) return;
        
        Dbg.o("acquire locks for field init", fd.init);
        boolean staticContext = Modifiers.isStatic(fd.modifiers);
        canAssignReadOnly = true;
        locks.mark();
        if (RccOptions.get().ihl) {
            if (staticContext) {
                locks.push(ClassLiteral.make(null, fd.getStartLoc()));
            } else {
                locks.push(ThisExpr.make(null, fd.getStartLoc()));
            }
        }
        if (RccOptions.get().ihnl && staticContext) {
            locks.push(LiteralExpr.make(
                TagConstants.NULLLIT,
                null,
                fd.getStartLoc()));
        }
        Env env = staticContext ? rootSEnv : rootIEnv;
        fd.init = checkInit(env, fd.init, fd.type);
        Dbg.o("release locks for field initialization", fd.init);
        locks.popToMark();
    }

    /**
     * Makes sure that we hold the `this' lock when checking
     * synchronized methods.
     */
    protected void checkRoutineDeclaration(RoutineDecl rd) {
        try {
            locks.mark();
            Dbg.o("typechecking routine " + rd.id());
            if (Modifiers.isSynchronized(rd.modifiers)) {
                Dbg.o("add lock for synchronized method " + rd.id());
                if (Modifiers.isStatic(rd.modifiers)) { 
                    locks.push(ClassLiteral.make(null, rd.getStartLoc()));
                } else {
                    locks.push(ThisExpr.make(null, rd.getStartLoc()));
                }
            } else if (rd instanceof ConstructorDecl) {
                if (RccOptions.get().chl) {
                    Dbg.o("add (implicit) lock for constructor " + rd.id());
                    locks.push(ThisExpr.make(null, rd.getStartLoc()));
                }
            }
            ExprVec expressions = getRequiresVec(rd);
            Dbg.o("add the locks required by the method contract", expressions);
            for (int i = 0; i < expressions.size(); i++) {
                locks.push(expressions.elementAt(i));
            }
            super.checkTypeDeclElem(rd);
        } finally {
            Dbg.o("remove locks used while typechecking the body of "+ rd.id());
            locks.popToMark();
        }
    }

    /**
     * Makes sure that proper lockas are considered held while checking
     * initialization blocks.
     */
    protected void checkInitBlock(InitBlock ib) {
        try {
            locks.mark();
            boolean staticContext = Modifiers.isStatic(ib.modifiers); 
            if (RccOptions.get().ihl) {
                Dbg.o("add (implicit) locks for the initializer in " + ib.parent.id);
                if (staticContext) {
                    locks.push(ClassLiteral.make(null, ib.getStartLoc()));
                } else {
                    locks.push(ThisExpr.make(sig, ib.getStartLoc()));
                }
            }
            if (RccOptions.get().ihnl && staticContext) {
                locks.push(LiteralExpr.make(
                    TagConstants.NULLLIT,
                    null,
                    ib.getStartLoc()));
            }
            canAssignReadOnly = true;
            super.checkTypeDeclElem(ib);
        } finally {
            Dbg.o("remove any locks used while typechecking initializer in " + ib.parent.id);
            locks.popToMark();
        }
    }

    // TODO: Comment this!
    // TODO: It looks like it could pay of to turn this into a template
    // method or something similar. There is a lot of common processing
    // but also pieces specific to universes (in javafe) and rcc (here).
    // Note that there are also some ESC/Java specific checks tangled in
    // the javafe code.
    // @ requires e != null && sig != null;
    protected void checkTypeDeclElem(/*@non_null*/ TypeDeclElem e) {
        Dbg.o("processing a " + TagConstants.toString(e.getTag()));
        switch (e.getTag()) {
        case TagConstants.FIELDDECL:
            super.checkTypeDeclElem(e);
            extraCheckFieldDecl((FieldDecl)e);
            break;
        case TagConstants.METHODDECL:
        case TagConstants.CONSTRUCTORDECL:
            checkRoutineDeclaration((RoutineDecl)e);
            break;
        case TagConstants.INITBLOCK:
            checkInitBlock((InitBlock)e);
            break;
        default:
            super.checkTypeDeclElem(e);
            break;
        }
    }
    
    /**
     * Get the locks required by a method.
     * 
     * @param rd The method.
     * @return The locks required by <code>rd</code>.
     */
    static protected ExprVec getRequiresVec(RoutineDecl rd) {
        ExprVec expressions = (ExprVec)requiresDecoration.get(rd);
        if (expressions == null) {
            Dbg.o("we use another typechecker to look at 'requires' of " + rd.id());
            inAnnotation = true;
            FlowInsensitiveChecks subChecker = 
                new FlowInsensitiveChecks((TypeSig)TypeSig.getSig(rd.parent), null);
            expressions = subChecker.checkRequiresVec(rd);
            inAnnotation = false;
        }
        return expressions;
    }

    // === Extensions to expression and statement checkers ===

    // TODO move the two branches in their own methods
    protected Env checkStmt(Env env, Stmt s) {
        if (inAnnotation) return env;
        int tag = s.getTag();
        // System.out.println("process stmt: " +
        // TagConstants.toString(s.getTag()));
        switch (tag) {
        case TagConstants.SYNCHRONIZESTMT:
            try {
                locks.mark();
                SynchronizeStmt ss = (SynchronizeStmt)s;
                ss.expr = checkFinalExpr(env, ss.expr, ss.expr.getStartLoc());
                Dbg.o("enter synchronize statement", ss.expr);
                locks.push(ss.expr);
                checkStmt(env, ss.stmt);
            } finally {
                Dbg.o("exit synchronize statement");
                locks.popToMark();
            }
            break;

        case TagConstants.CONSTRUCTORINVOCATION: {
            ConstructorInvocation ci = (ConstructorInvocation)s;
            env = super.checkStmt(env, s);
            if (ci == null || ci.decl == null) return env;
            ExprVec expressions = getRequiresVec(ci.decl);
            
            Dbg.o("typecheck constructor invocation" + ci.decl.id());
            Dbg.o("protected by", expressions);
            
            SubstitutionVec subs = SubstitutionVec.make();
            MultipleSubstitution ms = new MultipleSubstitution(subs);
            checkLocksHeld(
                ms,
                expressions,
                ci.getStartLoc(),
                ci.decl.pmodifiers);
            return env;
        }
        
        /*
        case TagConstants.RETURNSTMT:
            // Modify the return type to correspond to the proper instance
            ReturnStmt rs = (ReturnStmt)s;
            returnType = instanceTypeSig(env, returnType);
            super.checkStmt(env, s);
         */
        default:
            // new Exception().printStackTrace();
            env = super.checkStmt(env, s);
            break;
        }

        return env;
    }
    
    protected boolean lockHeld(MultipleSubstitution ms, Expr e) {
        CloneWithSubstitution c = new CloneWithSubstitution(ms);
        e = (Expr)c.clone(e, true);
        return locks.contains(e);
    }

    /**
     * Returns whether {@code expr} is a field access to a ghost field.
     * (It relies on FieldAccess.decl of the outermost---last---FieldAccess
     * and does not do any name resolution itself.)
     * @param expr The expression to check.
     * @return Whether {@code expr} is a ghost field.
     */
    /*private boolean isGhostAccess(Expr expr) {
        if (!(expr instanceof FieldAccess)) return false;
        FieldAccess fa = (FieldAccess)expr;
        if (fa.decl == null) return false;
        return GhostEnv.isGhostField(fa.decl);
    }*/

    protected void checkLocksHeld(
        MultipleSubstitution ms,
        ExprVec expressions,
        int line,
        ModifierPragmaVec mpv
    ) {
        Expr expr;

        // System.out.println ("---locks " + locks.toString());
        // System.out.println ("---substitutions " + ms.toString());
        // System.out.println ("---expressions " + expressions.toString());

        for (int i = 0; i < expressions.size(); i++) {
            expr = expressions.elementAt(i);
            //Dbg.o(expr);
            if (!lockHeld(ms, expr)) {
                CloneWithSubstitution c = new CloneWithSubstitution(ms);
                int declLoc = getLocInPragmas(expr, mpv);
                //Dbg.o(expr);
                expr = (Expr)c.clone(expr, true);
                //Dbg.o(expr);
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
        int line
    ) {
        Expr expr;

        // System.out.println ("---locks " + locks.toString());
        // System.out.println ("---substitutions " + ms.toString());
        // System.out.println ("---expressions " + expressions.toString());

        for (int i = 0; i < expressions.size(); i++) {
            expr = expressions.elementAt(i);
            //Dbg.o(expr);
            if (!lockHeld(ms, expr)) {
                CloneWithSubstitution c = new CloneWithSubstitution(ms);
                expr = (Expr)c.clone(expr, true);
                int declLoc = expr.getStartLoc(); // FIX TO PRINT RIGHT LOC
                ErrorMsg.print(sig, "Race", line, "Lock '"
                    + PrettyPrint.inst.toString(expr) + "' may not be held."
                    + "  Locks currently held are '" + locks + "'.", declLoc);
            }
        }
    }
    
    private void checkLocksHeld(ExprVec reqLocks, int useLoc, int declLoc) {
        Expr lock;
        MultipleSubstitution ms = new MultipleSubstitution();
        for (int i = 0; i < reqLocks.size(); ++i) {
            lock = reqLocks.elementAt(i);
            if (!lockHeld(ms, lock)) {
                ErrorMsg.print(
                    sig, 
                    "Race", 
                    useLoc, 
                    "Lock '" + PrettyPrint.inst.toString(lock) 
                      + "' may not be held. We only have '"
                      + locks + "'.", 
                    declLoc);
            }
        }
    }


    // DBG: private Hashtable dbgh = new Hashtable();


    /**
     * TODO The next two functions share a lot of code. Move it in a common place.
     * 
     * If a TypeSig is not attached to <code>e</code> then do nothing.
     * Otherwise interpret <code>t</code> as a TypeName, get the arguments,
     * typecheck them, and then gets the proper TypeSig instantiation.
     */
    private TypeSig instanceTypeSig(Env env, Expr e, Type t) {
        Dbg.o("getting instance for", t);
        Type type = getType(e);
        if (!(type instanceof TypeSig)) return null;
        Dbg.o("..good, we have a TypeSig");
        TypeSig ts = (TypeSig)type;
        if (ts.isInstance()) return ts;

        ASTDecoration argsDeco = PrepTypeDeclaration.typeArgumentDecoration;
        TypeName tn = (TypeName)t;
        ExprVec arguments = (ExprVec)argsDeco.get(tn);
        if (arguments == null) {
            arguments = ExprVec.make();
            argsDeco.set(tn, arguments);
        }
        checkLockExprVec(env, arguments, Location.NULL);
        ts = ts.getInstantiation(arguments);

        // TODO this should ensure that each argument is either a field access
        //      containing no ghost, or just one ghost. Otherwise unghosting 
        //      might diverge.
        
        Dbg.o("use " + ts.simpleName + " for expression", e);
        setType(e, ts);
        return ts;
    }
    
    private Type instanceTypeSig(Env env, Type t) {
        if (!(t instanceof TypeName)) return t;
        TypeName tn = (TypeName)t;
        TypeSig ts = (TypeSig)TypeSig.getSig(tn);
        if (ts.isInstance()) return ts;
        ASTDecoration argsDeco = PrepTypeDeclaration.typeArgumentDecoration;
        ExprVec arguments = (ExprVec)argsDeco.get(tn);
        if (arguments == null) {
            arguments = ExprVec.make();
            argsDeco.set(tn, arguments);
        }
        checkLockExprVec(env, arguments, Location.NULL);
        ts = ts.getInstantiation(arguments);
        TypeSig.setSig(tn, ts);
        return ts;
    }

    // === Begin: Custom typechecking ===
    
    protected Expr checkAmbiguousVariableAccessExpr(Env env, AmbiguousVariableAccess av) {
        Dbg.o("checking ambiguous var access", av);
        Expr r = super.checkAmbiguousVariableAccessExpr(env, av);
        Dbg.o("resolved to type " + r.getClass().getName());
        return r;
    }

    /**
     * Returns src[this->e]
     */
    private Expr replaceThisBy(Expr src, Expr e) {
        Substitution s = new Substitution(ThisExpr.make(null, Location.NULL), e);
        SubstitutionVec sv = SubstitutionVec.make();
        sv.addElement(s);
        MultipleSubstitution ms = new MultipleSubstitution(sv);
        CloneWithSubstitution cws = new CloneWithSubstitution(ms);
        Expr result = (Expr)cws.clone(src, true);
        Dbg.o("in expression", src);
        Dbg.o("..i transformed this into", e);
        Dbg.o("..and got", result);
        return result;
    }
    

    /**
     * Returns a field access equivalent to |e|, but which doesn't use
     * any ghost field. 
     *
     * (general form: alpha.x.y, g = ghost, f = normal field, alpha can be empty)
     *   unghost alpha.x.g = unghost alpha.(actual x g)
     *   unghost alpha.x.f = (unghost alpha.x).f
     *   unghost x = x
     * 
     * It only works if ghost arguments are either
     * a single ghost parameter or a field access with only normal
     * fields. That is why the procedure for typechecking arguments
     * should ensure these things hold. 
     * 
     * TODO Handle extending a ghostly class. Roughly: When you find a field
     *      you should decend from the class where it is declared to the static
     *      type and replace ghost parameters by ghost arguments while doing so.
     */
    private Expr unghost(Env env, Expr e) {
        // base case
        Dbg.o("unghosting", e);
        if (!(e instanceof FieldAccess)) return e;
        FieldAccess xy = (FieldAccess)e;
        if (!(xy.od instanceof ExprObjectDesignator)) return e;
        ExprObjectDesignator xeod = (ExprObjectDesignator)xy.od;
        Dbg.o("..good, it's a field access with an expression on the left");
        
        TypeSig ts = null;
        FieldAccess ax = null;
        if (xeod.expr instanceof VariableAccess) {
            VariableAccess va = (VariableAccess)xeod.expr;
            ts = instanceTypeSig(env, va, va.decl.type);
        } else if (xeod.expr instanceof FieldAccess) {
            ax = (FieldAccess)xeod.expr;
            ts = instanceTypeSig(env, ax, ax.decl.type);
        }
        if (ts == null) return e;
        Expr actual = ts.getActual(xy.id.toString());
        if (actual == null) {
            // y is a normal field
            xeod.expr = unghost(env, xeod.expr);
            return e;
        }
        if (xeod.expr instanceof VariableAccess) {
            // just return the actual, there's nothing else to do
            return actual;
        }
        if (!(ax.od instanceof ExprObjectDesignator)) return e;
        ExprObjectDesignator aeod = (ExprObjectDesignator)ax.od;
        Expr alpha = aeod.expr;
        actual = replaceThisBy(actual, alpha);
        actual = unghost(env, actual);
        return actual;
    }
    
    /*
     * NOTE Given the following inner class. 
     *   class A { 
     *     public class B { 
     *       public X x; //# guarded_by A.this 
     *     } 
     *   } 
     * The enclosing class is available only within B's scope (by using 
     * the syntax [A.this]). This means that within B's scope we can verify 
     * if a [synchronize(A.this)] statement exists or not.
     * However, any attempt to refer to x from other places (including from
     * class A) cannot be verified because we have no way of referring to B's
     * enclosing class and hence it is not possible for a _clearly_ good (at
     * compile time) synchronize statement to exist. Therefore, all such uses
     * should be flagged as errors.
     */
    // TODO How to handle other nested classes (e.g., static nested)?
    // TODO Clarify how access modifiers impact the reasoning above.
    /**
     * Typechecks field access. Unlike the overriden method it also takes into
     * account ghost fields.
     * 
     * @param env The environment in which to typecheck.
     * @param fa The field access to typecheck.
     * @return The typechecked field access.
     */
    // @ ensures getTypeOrNull(\result) != null;
    protected FieldAccess checkFieldAccessExpr(
        /*@non_null*/ Env env,
        /*@non_null*/ FieldAccess fa
    ) {
        // First do normal typechecking 
        // (and recursively check the locks on the object designator)
        fa = super.checkFieldAccessExpr(env, fa);
        if (fa == null || fa.decl == null || inAnnotation) return fa;
        Dbg.o("typecheck access to field", fa.decl);

        // Eliminate ghosts from the required locks
        ExprVec reqLocks = getGuardedVec(fa.decl);
        ExprVec realLocks = ExprVec.make();
        if (fa.od instanceof ExprObjectDesignator)
        {
            ExprObjectDesignator eod = (ExprObjectDesignator)fa.od;
            for (int i = 0; i < reqLocks.size(); ++i) {
                Expr l = reqLocks.elementAt(i);
                l = replaceThisBy(l, eod.expr);
                l = unghost(env, l);
                realLocks.addElement(l);
            }
        } else {
            Dbg.o("..this is a funny field access");
            realLocks = reqLocks;
        }
        Dbg.o("we should have the locks", realLocks);
        checkLocksHeld(realLocks, fa.getStartLoc(), fa.decl.getStartLoc());
        
        // remember the proper typesig for this 
        // (used for example for checking assignments)
        instanceTypeSig(env, fa, fa.decl.type);
        
        return fa;
    }
    
    /** Just remember the proper instantiation for it. */
    protected Expr checkVariableAccessExpr(Env env, VariableAccess lva) {
        Expr r = super.checkVariableAccessExpr(env, lva);
        instanceTypeSig(env, lva, lva.decl.type);
        return r;
    }
    protected Env checkVarDeclStmt(Env e, LocalVarDecl s) {
        if (s.init != null) Dbg.o("init: " + s.init.getClass().getName());
        return super.checkVarDeclStmt(e, s);
    }

    
    /**
     * Get the real locks for a routine invocation, given the required
     * locks (which appear on the routine declaration). If <code>prefix</code>
     * is not an instance of <code>ExprObjectdesignator</code> then it
     * is ignored.
     * 
     * For each lock which is a variable access we try to identify its actual
     * argument. Otherwise we assume it is a FieldAccess or ThisExpr,
     * prefix it, and unghost it.
     */
    //@ requires parameters.size() == arguments.size();
    private ExprVec getRealRoutineLocks(
        Env env,
        ObjectDesignator prefix,
        /*@non_null*/ FormalParaDeclVec parameters, 
        /*@non_null*/ ExprVec arguments, 
        ExprVec reqLocks
    ) {
        Assert.notFalse(parameters.size() == arguments.size());
        
        // preprocessing: map parameter names to arguments
        Hashtable argumentFor = new Hashtable(5);
        for (int i = 0; i < arguments.size(); ++i) {
            FormalParaDecl p = parameters.elementAt(i);
            Expr a = arguments.elementAt(i);
            argumentFor.put(p.id.toString(), a);
        }
        
        // process required locks one-by-one
        ExprVec realLocks = ExprVec.make();
        
        // TODO treat static(Context) properly
        for (int i = 0; i < reqLocks.size(); ++i) {
            Expr l = reqLocks.elementAt(i);
            if (l instanceof VariableAccess) {
                // it must be a parameter; replace it by the argument
                VariableAccess va = (VariableAccess)l;
                l = (Expr)argumentFor.get(va.id.toString());
            } else {
                // we assume it's a field access (also handles 'this' just fine)
                if (prefix instanceof ExprObjectDesignator) {
                    ExprObjectDesignator eod = (ExprObjectDesignator)prefix;
                    l = replaceThisBy(l, eod.expr);
                }
                l = unghost(env, l);
            }
            realLocks.addElement(l);
        }
        Dbg.o("the 'real' locks are", realLocks);
        
        return realLocks;
    }

    /**
     * Check that the locks required by a method are indeed held.
     * 
     * @param env The environment in which to typecheck.
     * @param mi The method invocation to typecheck.
     * @return The typechecked method invocation.
     */
    // TODO: Annotate this!
    protected MethodInvocation checkMethodInvocationExpr(
        /*@non_null*/ Env env,
        /*@non_null*/ MethodInvocation mi
    ) {
        mi = super.checkMethodInvocationExpr(env, mi);
        if (mi == null || mi.decl == null || inAnnotation) return mi; 
        
        Dbg.o("typecheck method invocation", mi);
        ExprVec reqLocks = getRequiresVec(mi.decl);
        ExprVec realLocks = getRealRoutineLocks(env, mi.od, mi.decl.args, mi.args, reqLocks);
        checkLocksHeld(realLocks, mi.getStartLoc(), mi.decl.getStartLoc());
        // remember the proper typesig for this 
        // (used for example for checking assignments)
        instanceTypeSig(env, mi, mi.decl.returnType);
        return mi;
    }

    /**
     * Check that the locks required by a constructor are held.
     * 
     * @param env The environment in which to check the new expression.
     * @param ne The new expression to typecheck.
     * @return The environment after the new expression.
     */
    // TODO: Annotate this!
    protected NewInstanceExpr checkNewInstanceExpr(
        /*@non_null*/ Env env,
        /*@non_null*/ NewInstanceExpr ne
    ) {
        ne = super.checkNewInstanceExpr(env, ne);
        if (ne == null || ne.decl == null || inAnnotation) return ne;
        
        Dbg.o("typecheck instantiation", ne);
        ExprVec reqLocks = getRequiresVec(ne.decl);
        ExprVec realLocks = getRealRoutineLocks(env, null, ne.decl.args, ne.args, reqLocks);
        checkLocksHeld(realLocks, ne.getStartLoc(), ne.decl.getStartLoc());
        // remember the proper typesig for this 
        // (used for example for checking assignments)
        instanceTypeSig(env, ne, ne.type);
        return ne;
    }

    /**
     * Check that the locks on the element of the array are held.
     * 
     * @param env The environment in which to typecheck.
     * @param r The array reference to typecheck.
     * @return The typechecked array reference.
     */
    // @ ensures getTypeOrNull(\result) != null;
    protected ArrayRefExpr checkArrayRefExpr(
    /* @ non_null */Env env,
    /* @ non_null */ArrayRefExpr r) {
        r = super.checkArrayRefExpr(env, r);

        Type t = getType(r.array);
        if (!inAnnotation && t instanceof ArrayType) {
            Dbg.o("type-check array ref", t);
            ExprVec reqLocks = getElemGuardedVec(t, env);
            ExprVec realLocks = ExprVec.make();
            Expr prefix = getPrefix(r);
            for (int i = 0; i < reqLocks.size(); ++i) {
                Expr l = reqLocks.elementAt(i);
                if (prefix != null) l = replaceThisBy(l, prefix);
                l = unghost(env, l);
                realLocks.addElement(l);
            }
            checkLocksHeld(realLocks, r.locOpenBracket, Location.NULL);
        }

        return r;
    }
    
    /**
     * Returns the object designator (if any) as an expression. Descends
     * into ArrayRefExpr. Returns null if a proper object designator is
     * not found.
     */
    private Expr getPrefix(Expr e) {
        if (e instanceof ArrayRefExpr) {
            ArrayRefExpr a = (ArrayRefExpr)e;
            return getPrefix(a.array);
        }
        if (e instanceof FieldAccess) {
            FieldAccess fa = (FieldAccess)e;
            if (fa.od instanceof ExprObjectDesignator) {
                ExprObjectDesignator eod = (ExprObjectDesignator)fa.od;
                return eod.expr;
            }
        }
        return null;
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
     * constructors, and fields.
     */
    public Env checkModifierPragmaVec(ModifierPragmaVec mod, ASTNode a, Env env) {
        switch (a.getTag()) {
        case TagConstants.METHODDECL:
        case TagConstants.CONSTRUCTORDECL:
            RoutineDecl rd = (RoutineDecl)a;
            getRequiresVec(rd);
            break;
        case TagConstants.FIELDDECL:
            FieldDecl fd = (FieldDecl)a;
            getGuardedVec(fd);
            break;
        case TagConstants.CLASSDECL:
        case TagConstants.INTERFACEDECL:
            getLocalThreadStatus((TypeDecl)a, env);
            break;
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
        Env env
    ) {
        getElemGuardedVec((Type)a, env);
        return env;
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
        Env env
    ) {
        inAnnotation = true;
        int tag = p.getTag();
        switch (tag) {
        case TagConstants.ARRAYGUARDMODIFIERPRAGMA: {
            ArrayGuardModifierPragma rp = (ArrayGuardModifierPragma)p;
            checkLockExprVec(env, rp.expressions, rp.getStartLoc());
            //Dbg.o(rp.expressions);
            if (ctxt.getTag() != TagConstants.ARRAYTYPE) {
                ErrorMsg.print(
                    sig,
                    "Modifiers",
                    ctxt.getStartLoc(),
                    "only array declarations may contain this type of annotation.",
                    Location.NULL);
            }
            ExprVec g = (ExprVec)elemGuardDecoration.get(ctxt);
            for (int i = 0; i < rp.expressions.size(); i++) {
                g.addElement(rp.expressions.elementAt(i));
            }
            //Dbg.o(g);
            break;
        }
        case TagConstants.GENERICARGUMENTPRAGMA:
            // Handled in PrepTypeDeclaration
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
        
        Dbg.o("process modifier pragma " + p.toString());

        inAnnotation = true; // Must be reset before we exit!
        int tag = p.getTag();
        switch (tag) {
        case TagConstants.READONLYMODIFIERPRAGMA:
            // TODO: Comment this!
            break;

        case TagConstants.REQUIRESMODIFIERPRAGMA: {
            RequiresModifierPragma rp = (RequiresModifierPragma)p;
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
            ExprVec g = (ExprVec)requiresDecoration.get(ctxt);
            for (int i = 0; i < rp.expressions.size(); i++) {
                g.addElement(rp.expressions.elementAt(i));
            }
            break;
        }
        case TagConstants.GUARDEDBYMODIFIERPRAGMA: {
            if (ctxt.getTag() == TagConstants.CLASSDECL) break; // already done
            GuardedByModifierPragma rp = (GuardedByModifierPragma)p;
            //Dbg.o(rp.expressions);
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
            ExprVec g = (ExprVec)guardDecoration.get(ctxt);
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
                ((ThreadLocalStatusPragma)p).local));
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
        
        switch (s.getTag()) {
        case TagConstants.HOLDSSTMTPRAGMA: {
            HoldsStmtPragma cs = (HoldsStmtPragma)s;
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
            return super.checkStmtPragma(env, s);
        }
        inAnnotation = false;
        return env;
    }

    /**
     * This method should be called once per routine declaration.
     * It checks whether the requires set is a subset of that for
     * the overriden method.
     * 
     * The |requiresDecoration| on the method declaration is used by
     * |getRequiresVec| to decide whether to call this method or not
     * (i.e., this is the mechanism for calling this once per method.)
     * 
     * As a side effect (why?) the pragma modifiers for the type that
     * encloses |rd| are processed.
     * 
     * TODO It also used to do some strange-looking processing on formal
     *      parameters. Now it is commented out until I figure out what should
     *      happen.
     * 
     */
    protected ExprVec checkRequiresVec(RoutineDecl rd) {
        
        ExprVec g = ExprVec.make();

        requiresDecoration.set(rd, g);
        TypeSig s = (TypeSig)TypeSig.getSig(rd.parent);

        Assert.precondition(!s.isInstance());
        Dbg.o("state is " + s.state + " for " + s.simpleName);
        Assert.precondition(s.state >= TypeSig.PREPPED);

        // Set up variables for entire traversal
        sig = s;
        rootSEnv = makeEnvForTypeSig(s, true); // @ nowarn Invariant
        rootIEnv = makeEnvForTypeSig(s, false); // @ nowarn Invariant
        boolean staticContext = Modifiers.isStatic(rd.modifiers);

        Env env = staticContext ? rootSEnv : rootIEnv;

        leftToRight = false;

        // add params (because they can be required)
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
            Dbg.o("added formal to environment (for checking requires)", formal);
        }

        // Collect the requires clauses. Use the base class method to
        // make sure (only) |checkModifierPragma| is called for each pragma.
        Dbg.o("collect requires clausses for " + rd.id());
        super.checkModifierPragmaVec(rd.pmodifiers, rd, env);

        // check overridden expr ved
        if (rd instanceof MethodDecl) {
            Dbg.o("check that requires are not stronger than the ones inherited by " + rd.id());
            MethodDecl md = (MethodDecl)rd;
            Set methods = javafe.tc.PrepTypeDeclaration.getInst().getOverrides(
                md);
            Enumeration e = methods.elements();
            while (e.hasMoreElements()) {
                MethodDecl m = (MethodDecl)e.nextElement();
                ExprVec superExpressions = getRequiresVec(m);
                ExprVec expressions = (ExprVec)requiresDecoration.get(rd);
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
        EqualsASTNoDecl eqNoDecl = new EqualsASTNoDecl();

        for (int i = 0; i < exps.size(); ++i) {
            Expr ei = exps.elementAt(i);
            for (int j = i + 1; j < exps.size(); ++j) {
                Expr ej = exps.elementAt(j);
                if (eqNoDecl.equals(ei, ej)) return true;
            }
        }

        return false;
    }

    public ExprVec checkGuardedVec(FieldDecl fd) {
        ExprVec g = ExprVec.make();
        guardDecoration.set(fd, g);
        TypeSig s = (TypeSig)TypeSig.getSig(fd.parent);
        Dbg.o("checking the guarded_by part of", fd);

        Assert.precondition(s.state >= TypeSig.PREPPED);

        // Set up variables for entire traversal
        sig = s;
        rootSEnv = makeEnvForTypeSig(s, true); // @ nowarn Invariant
        rootIEnv = makeEnvForTypeSig(s, false); // @ nowarn Invariant
        boolean staticContext = Modifiers.isStatic(fd.modifiers);

        Env env = staticContext ? rootSEnv : rootIEnv;

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
        // Dbg.o(g);

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
        ExprVec expressions = (ExprVec)guardDecoration.get(fd);
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

    /**
     * TODO comment better
     * This is the javafe.tc.FlowInsensitiveChecks.checkTypeModifierPragmaVec
     * and is also used elsewhere.
     */
    static public ExprVec getElemGuardedVec(Type t, Env env) {
        ExprVec expressions = (ExprVec)elemGuardDecoration.get(t);
        // Dbg.o(t); Dbg.o(expressions);
        if (env == null) {
            env = (Env)Env.typeEnv.get(t);
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
            // Dbg.o(expressions);
            inAnnotation = false;
        }
        // Dbg.o(locks);
        return expressions;
    }

    // === Pragma checkers : end ===

    protected Expr checkFinalExpr(Env env, Expr expr, int assocLoc) {
        Assert.notFalse(expr != null);
        boolean prev = inAnnotation; inAnnotation = true;
        Expr checkExpr = checkExpr(env, expr, Types.javaLangObject());
        inAnnotation = prev;
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
        Dbg.o("checking these locks", expressions);
        boolean prev = inAnnotation; inAnnotation = true;
        for (int i = 0; i < expressions.size(); i++) {
            Expr expr = expressions.elementAt(i);
            Expr checkExpr = checkFinalExpr(env, expr, assocLoc);
            Dbg.o("lock type before is " + expr.getClass().getName(), expr);
            Dbg.o("lock type after is" + checkExpr.getClass().getName(), checkExpr);
            expressions.setElementAt(checkExpr, i);
        }
        inAnnotation = prev;
    }

    protected void addToLockStack(ExprVec expressions) {
        for (int i = 0; i < expressions.size(); i++) {
            Expr expr = expressions.elementAt(i);
            locks.push(expr);
        }
    }

    // === Utility routines : begin ===

    /**
     * Copy the Type associated with an expression by the typechecking pass
     * to another Expr. This is used by Substitute to ensure it returns an
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
            MethodDecl directMD = (MethodDecl)(e.nextElement());
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
        MethodDecl md = (MethodDecl)rd;
        MethodDecl override = null;
        Set direct = javafe.tc.PrepTypeDeclaration.getInst().getOverrides(md);
        Enumeration e = direct.elements();
        while (e.hasMoreElements()) {
            MethodDecl directMD = (MethodDecl)(e.nextElement());
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
            VariableAccess lva = (VariableAccess)expr;
            return Modifiers.isFinal(lva.decl.modifiers)
                || readOnlyPragma(lva.decl.pmodifiers) != null;

        }
        case TagConstants.FIELDACCESS: {
            FieldAccess fa = (FieldAccess)expr;
            if (!isFinalObjectDesignator(env, fa.od)) {
                return false;

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
            return isFinalExpr(env, ((ExprObjectDesignator)od).expr);
        }

        default:
            return true;
        }
    }

    // assume javafe.tc.flowinsens.checkObjDes has already been called
    protected Type getObjectDesignatorType(Env env, ObjectDesignator od) {

        switch (od.getTag()) {

        case TagConstants.EXPROBJECTDESIGNATOR: {
            ExprObjectDesignator eod = (ExprObjectDesignator)od;
            return getType(eod.expr);
        }

        case TagConstants.TYPEOBJECTDESIGNATOR: {
            TypeObjectDesignator tod = (TypeObjectDesignator)od;
            // Type has been created by disambiguation code, so it is ok.

            Type t = tod.type;
            if (t instanceof TypeName) t = TypeSig.getSig((TypeName)t);
            Assert.notFalse(t instanceof TypeSig); // @ nowarn Pre
            return t;
        }

        case TagConstants.SUPEROBJECTDESIGNATOR: {
            TypeDecl d = sig.getTypeDecl();
            TypeSig superSig = (TypeSig)TypeSig.getSig(((ClassDecl)d).superClass); // @
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
                RequiresModifierPragma rmp = (RequiresModifierPragma)mp;
                if (rmp.expressions.contains(expr)) {
                    return rmp.getStartLoc();
                }
            } else if (mp instanceof GuardedByModifierPragma) {
                GuardedByModifierPragma gmp = (GuardedByModifierPragma)mp;
                if (gmp.expressions.contains(expr)) {
                    return gmp.getStartLoc();
                }
            }
        }
        return Location.NULL;
    }

    /** *** thread local ********* */

    static public boolean getLocalThreadStatus(TypeDecl d, Env env) {
        Boolean b = (Boolean)threadLocalDecoration.get(d);
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
        Boolean b = ((Boolean)threadLocalDecoration.get(d));

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
            + (((Boolean)threadLocalDecoration.get(d)).booleanValue() ? "thread local"
                : "thread shared") + "]");

        commonThreadLocal(env, d);

        return ((Boolean)threadLocalDecoration.get(d));
    }

    private boolean guardPragmaExists(ModifierPragmaVec m) {
        if (m == null) return false;
        for (int i = 0; i < m.size(); i++) {
            if (m.elementAt(i) instanceof GuardedByModifierPragma) {
                return true;
            }
        }
        return false;
    }

    private ReadOnlyModifierPragma readOnlyPragma(ModifierPragmaVec m) {
        if (m == null) return null;
        for (int i = 0; i < m.size(); i++) {
            if (m.elementAt(i) instanceof ReadOnlyModifierPragma) {
                return (ReadOnlyModifierPragma)m.elementAt(i);
            }
        }
        return null;
    }

    private boolean requiresPragmaExists(ModifierPragmaVec m) {
        if (m == null) return false;
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
        TypeModifierPragmaVec m = ((ArrayType)a).tmodifiers;
        if (m == null) return false;
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
        TypeModifierPragmaVec m = ((ArrayType)a).tmodifiers;
        if (m == null) return false;
        for (int i = 0; i < m.size(); i++) {
            if (m.elementAt(i) instanceof ArrayGuardModifierPragma) {
                return arrayGuarded(((ArrayType)a).elemType);
            }
        }
        return false;
    }

    public void commonThreadLocal(Env env, TypeDecl d) {
        TypeDeclElem elem;

        for (int i = 0; i < d.elems.size(); i++) {
            elem = d.elems.elementAt(i);
            if (elem.getTag() == TagConstants.FIELDDECL) {
                FieldDecl fd = (FieldDecl)elem;
                if (Modifiers.isStatic(fd.modifiers)) {
                    if (fd.type instanceof TypeSig) {
                        TypeDecl decl = ((TypeSig)fd.type).getTypeDecl();
                        if (getLocalThreadStatus(decl, env)) {
                            ErrorMsg.print(
                                sig,
                                TypeSig.getSig(d),
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
                MethodDecl md = (MethodDecl)elem;
                // if ( isMethodOverride(md)) {
                Set methods = javafe.tc.PrepTypeDeclaration.getInst().getOverrides(
                    md);

                Enumeration e = methods.elements();
                while (e.hasMoreElements()) {

                    MethodDecl superDecl = (MethodDecl)e.nextElement();
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
                FieldDecl fd = (FieldDecl)elem;
                if (guardPragmaExists(fd.pmodifiers)
                    || elementGuardPragmaExists(((FieldDecl)elem).type)) {
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

    // TODO rewrite this---too complicated
    public void checkThreadShared(Env env, TypeDecl d) {
        TypeDeclElem elem;
        boolean unsharedFieldSeen = false;

        if (d instanceof ClassDecl && ((ClassDecl)d).superClass != null) {
            TypeDecl parent = env.resolveTypeName(
                null,
                ((ClassDecl)d).superClass) // TODO: check
                .getTypeDecl();
            if (parent != null && getLocalThreadStatus(parent, env)) {
                ErrorMsg.print(
                    sig,
                    TypeSig.getSig(parent),
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
                FieldDecl fd = (FieldDecl)elem;
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
                            if (!Modifiers.isStatic(fd.modifiers) 
                                && !Modifiers.isVolatile(fd.modifiers)) {
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
                    type = TypeSig.getSig((TypeName)fd.type);
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
                    type = (javafe.tc.TypeSig)fd.type;
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
                Types.getJavaLang("Thread"))) {
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
                FieldDecl fd = (FieldDecl)elem;
                if (guardPragmaExists(fd.pmodifiers)) {
                    return true;
                }
                break;

            case TagConstants.METHODDECL:
                MethodDecl md = (MethodDecl)elem;
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
     * Verifies that readonly variables are not written to when
     * <code>!canAssignReadOnly</code>. Other parts of this class are
     * responsible for resetting <code>canAssignReadOnly</code> when we are in
     * in a lvalue position.
     */
    protected Expr checkDesignator(Env env, Expr e) {
        e = super.checkDesignator(env, e);
        
        if (canAssignReadOnly) return e;

        // check readonly
        ReadOnlyModifierPragma romp = null;
        // System.out.println("checkDesignator " + e);
        switch (e.getTag()) {
        case TagConstants.VARIABLEACCESS:
            VariableAccess lva = (VariableAccess)e;
            romp = readOnlyPragma(lva.decl.pmodifiers);
            break;
        case TagConstants.FIELDACCESS:
            FieldAccess fa = (FieldAccess)e;
            try {
                FieldDecl fd = Types.lookupField(
                    getObjectDesignatorType(env, fa.od), 
                    fa.id, 
                    sig);
                romp = readOnlyPragma(fd.pmodifiers);
            } catch (LookupException le) {
                // The field might be duplicated.
                Assert.notFalse(ErrorSet.errors != 0);
            }
            break;
        }
        if (romp != null) {
            ErrorMsg.print(
                sig,
                "ReadOnly",
                e.getStartLoc(),
                "Assigning a variable declared as readonly",
                romp.getStartLoc());
        }
        return e;
    }

    // === Utility routines : end ===

    // === Testing and debugging : begin ===
    
    //static private Logger log = Logger.getLogger("rcc.tc");

    public static void main(String[] args) {
        // TODO: Implement this!
    }

    // === Testing and debugging : end ===

}
