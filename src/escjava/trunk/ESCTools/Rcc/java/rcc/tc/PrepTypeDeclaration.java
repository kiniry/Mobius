/* Copyright 2000, 2001, Compaq Computer Corporation */

package rcc.tc;

import java.util.Hashtable;

import javafe.ast.ASTDecoration;
import javafe.ast.ASTNode;
import javafe.ast.AmbiguousVariableAccess;
import javafe.ast.ClassDecl;
import javafe.ast.Expr;
import javafe.ast.ExprObjectDesignator;
import javafe.ast.ExprVec;
import javafe.ast.FieldAccess;
import javafe.ast.FieldDecl;
import javafe.ast.FieldDeclVec;
import javafe.ast.FormalParaDecl;
import javafe.ast.FormalParaDeclVec;
import javafe.ast.Identifier;
import javafe.ast.InterfaceDecl;
import javafe.ast.MethodDecl;
import javafe.ast.MethodDeclVec;
import javafe.ast.ModifierPragma;
import javafe.ast.ModifierPragmaVec;
import javafe.ast.Modifiers;
import javafe.ast.PrettyPrint;
import javafe.ast.SimpleName;
import javafe.ast.ThisExpr;
import javafe.ast.TypeDecl;
import javafe.ast.TypeDeclElem;
import javafe.ast.TypeDeclElemVec;
import javafe.ast.TypeModifierPragma;
import javafe.ast.TypeModifierPragmaVec;
import javafe.ast.TypeName;
import javafe.ast.TypeNameVec;
import javafe.tc.Env;
import javafe.tc.EnvForCU;
import javafe.tc.EnvForTypeSig;
import javafe.util.Assert;
import javafe.util.ErrorSet;
import javafe.util.Info;
import javafe.util.Location;
import rcc.ast.CloneAST;
import rcc.ast.CloneForInstantiation;
import rcc.ast.CloneWithSubstitution;
import rcc.ast.EqualsAST;
import rcc.ast.EqualsASTNoDecl;
import rcc.ast.GenericArgumentPragma;
import rcc.ast.GenericParameterPragma;
import rcc.ast.GhostDeclPragma;
import rcc.ast.MultipleSubstitution;
import rcc.ast.Substitution;
import rcc.ast.SubstitutionVec;
import rcc.ast.TagConstants;

/**
 * NOTE According to the contract of <code>javafe.tc.Typesig</code> this
 *      class shall not use <code>FlowInsensitiveChecks</code> to avoid
 *      call cycles.
 *      
 * NOTE Below I use `parameters' as a shorthand for `formal parameters'
 *      and `arguments' as a shorthand for `actual arguments'.
 *
 * See below for some clarifications on 
 * <code>javafe.tc.PrepTypeDeclaration</code>.
 * 
 * The responsabilities of this class include:
 *  - Transforms the GENERICARGUMENTPRAGMA pragma type modifiers of 
 *    (as in C<x> f) into GenericArgumentPragma and attach it as a decoration
 *    on the type name (C). 
 *  - Each (class) ghost parameter is transformed into a field declaration
 *    whose parent is the current class declaration and which are attached 
 *    as a GhostDeclPragma decoration to the current class declaration.
 *  - Uses the processTypeNameAnnotations hook to change resolution so
 *    that the signature of the proper instantiation is returned, instead
 *    of the signature of the generic type when resolving names such as C<x>. 
 *  - Informs the default instantiation TypeSig what its formal parameters are.
 *
 * We override the following methods for unknown reasons:
 *  - getEnvForCurrentSig
 *  
 * We override the following so that we transform generic arguments into
 * AST decorations and we create TypeSig instantiations.
 *  - processTypeNameAnnotations
 *
 * We override the following methods to process generic parameters into
 * field declarations added as decorations to the type declaration.
 *  - visitClassDecl
 *  - visitInterfaceDecl
 *
 * The following notes should accompany 
 *   <code>javafe.tc.PrepTypeDeclaration</code>,
 * but at the moment I'm unwilling to touch that.
 *
 * This class is used by <code>FlowInsensitiveChecks</code> to identify
 * members of types, including inherited ones. It is also used for related
 * queries such as `what are (all) the methods overriden by method X?'.
 * 
 * As the doc in <code>javafe.tc.PrepTypeDeclaration</code> says, this
 * is where typechecking at signature level is done. This means everything
 * that can be checked without looking in bodies (of constructors, methods,
 * and static blocks) is checked here. As a side-effect of these checks
 * the TypeSig is `informed' what are its fields, its methods, and
 * its constructors (as declarations). 
 * 
 * The `main' method is <code>PrepTypeDeclaration.prepTypeSignature</code>.
 *
 * TODO Many methods have package visibility. It looks more like an accident.
 */
public class PrepTypeDeclaration extends javafe.tc.PrepTypeDeclaration {

    public PrepTypeDeclaration() {
        inst = this;
    } // @ nowarn Invariant

    /**
     * TODO remove the functionality of having guarded_by per class
     * 
     * Look at all field declarations in type {@code d} and clone
     * their pragma modifiers. Conceptually, the code 
     * {@code A x,y guarded_by l;} is transformed into
     * {@code A x guarded_by l; A y guarded_by l;}.
     * 
     *  Also takes guarded_by annotations on a class and replicates it
     *  on all non-final field declarations.
     */
    public void addClassGuardsToFields(TypeDecl d) {
        // add class guards

        if (d.pmodifiers == null) return;

        // clone because pragmas may be shared between fields, ie Foo f,g,h;
        CloneAST clone = new CloneAST();
        for (int i = 0, sz = d.elems.size(); i < sz; i++) {
            TypeDeclElem e = d.elems.elementAt(i);
            if (e instanceof FieldDecl) {
                FieldDecl fd = (FieldDecl)e;
                ModifierPragma t[] = fd.pmodifiers.toArray();
                for (int j = 0; j < t.length; j++) {
                    t[j] = (ModifierPragma)clone.clone(t[j], true);
                }
                fd.pmodifiers = ModifierPragmaVec.make(t);
            }
        }
        
        for (int j = 0; j < d.pmodifiers.size(); j++) {
            ModifierPragma p = d.pmodifiers.elementAt(j);
            if (p.getTag() == TagConstants.GUARDEDBYMODIFIERPRAGMA) {
                for (int i = 0; i < d.elems.size(); i++) {
                    TypeDeclElem e = d.elems.elementAt(i);
                    if (e instanceof FieldDecl) {
                        FieldDecl fd = (FieldDecl)e;
                        if (!Modifiers.isFinal(fd.modifiers)) {
                            fd.pmodifiers.addElement(p);
                        }
                    }
                }
            }
        }
    }

    /**
     * Returns whether there are any ghost parameters on this class;
     * that is, whether it is a 'generic' class.
     * @param sig The type signature of the class to check.
     * @return True iff {@code sig} is generic.
     */
    public boolean hasParameters(javafe.tc.TypeSig sig) {
        if (typeParametersDecoration.get(sig) != null) {
            return true;
        }

        // look for type parameters
        TypeModifierPragmaVec v = sig.getTypeDecl().tmodifiers;
        if (v != null) {
            for (int i = 0; i < v.size(); i++) {
                if (v.elementAt(i).getTag() == TagConstants.GENERICPARAMETERPRAGMA) {
                    return true;
                }
            }
        }
        return false;
    }

    public void prepGenericTypeDecl(TypeSig s) {
        TypeDecl decl = s.getTypeDecl();

        checkTypeModifiers(decl, s, true);
        checkTypeModifierPragmaVec(
            decl.tmodifiers, 
            decl, 
            getEnvForCurrentSig(s, true), 
            s);
    }

    /**
     * TODO comment this!
     */
    // @ requires decl!=null && currentSig!=null
    public void visitClassDecl(ClassDecl decl, javafe.tc.TypeSig currentSig) {
        if (!hasParameters(currentSig)) { 
            addClassGuardsToFields(decl);
        }
        checkTypeModifierPragmaVec(
            decl.tmodifiers, 
            decl, 
            getEnvForCurrentSig(currentSig, true), 
            currentSig);
        super.visitClassDecl(decl, currentSig);
    }

    // @ requires decl!=null && currentSig!=null
    public void visitInterfaceDecl(
        InterfaceDecl decl,
        javafe.tc.TypeSig currentSig
    ) {
        addClassGuardsToFields(decl);
        checkTypeModifierPragmaVec(
            decl.tmodifiers, 
            decl, 
            getEnvForCurrentSig(currentSig, true),
            currentSig);
        super.visitInterfaceDecl(decl, currentSig);
    }

    static public ASTDecoration typeParametersDecoration = new ASTDecoration(
        "type parameters");

    static public ASTDecoration parameterDeclDecoration = new ASTDecoration(
        "decl for parameter");

    // @ requires env!=null
    protected void checkTypeModifierPragmaVec(
        TypeModifierPragmaVec v,
        ASTNode ctxt,
        Env env,
        javafe.tc.TypeSig currentSig
    ) {
        if (v != null) for (int i = 0; i < v.size(); i++)
            checkTypeModifierPragma(v.elementAt(i), ctxt, env, currentSig);
    }

    /**
     * Transforms ghost annotations into field declarations and wraps them in
     * <code>GhostDeclPragma</code> nodes. A link from the ghost annotation
     * to the newly introduced fields is kept by the {@code parameterDeclDecoration}.
     */
    // @ requires p!=null && env!=null
    protected void checkTypeModifierPragma(
        TypeModifierPragma p,
        ASTNode ctxt,
        Env env,
        javafe.tc.TypeSig currentSig
    ) {
        int tag = p.getTag();
        switch (tag) {
        case TagConstants.GENERICPARAMETERPRAGMA: {
            GenericParameterPragma pp = (GenericParameterPragma)p;
            Object pd = typeParametersDecoration.get(currentSig);
            if (pd != null && pd != pp.args) {
                ErrorSet.error(
                    ctxt.getStartLoc(),
                    "can only have one type parameter list  for class or interface declaration.");
            }
            if (pd != null) return;

            typeParametersDecoration.set(currentSig, pp.args);
            for (int i = 0; i < pp.args.size(); i++) {
                FormalParaDecl parameter = pp.args.elementAt(i);
                env.resolveType(currentSig, parameter.type);
                FieldDecl decl = FieldDecl.make(
                    parameter.modifiers | Modifiers.ACC_FINAL,
                    parameter.pmodifiers,
                    parameter.id,
                    parameter.type,
                    parameter.locId,
                    null,
                    Location.NULL);
                decl.setParent((TypeDecl)ctxt);
                GhostDeclPragma pragma = GhostDeclPragma.make(
                    decl,
                    parameter.locId);
                ((TypeDecl)ctxt).elems.insertElementAt(pragma, 0);
                parameterDeclDecoration.set(parameter, decl);
            }
            break;
        }
        default:
            Assert.fail("Unexpected tag " + tag);
        }
    }

    static protected InstantiationVec instantiations = InstantiationVec.make();

    /**
     * TODO Comment this!
     */
    static protected EqualsASTNoDecl equality = new EqualsAST();

    static public final ASTDecoration typeArgumentDecoration = new ASTDecoration(
        "type args");

    static Hashtable declsForInstantiations = new Hashtable();

    /**
     * Look up in <code>instantiations</code> one that matches
     * <code>sig</code> instantiated with arguments <code>expressions</code>.
     * 
     * @return The cached instantiation, if one exists; null otherwise.
     */
    protected javafe.tc.TypeSig findInstantiation(
        javafe.tc.TypeSig sig,
        ExprVec expressions
    ) {
        for (int i = 0; i < instantiations.size(); i++) {
            Instantiation instantiation = instantiations.elementAt(i);
            if (instantiation.sig == sig
                && equality.equals(instantiation.expressions, expressions)) {
                return instantiation.instantiation;
            }
        }
        return null;
    }

    /**
     * Transform type modifier pragmas into type argument decorations,
     * if it hasn't been already done.
     *  
     * @param tn The type name to process.
     */
    protected void processGenericArgumentPragmas(TypeName tn) {
        Info.out("[process formal params for " + tn.name.printName() + "]");
        ExprVec expressions = (ExprVec)typeArgumentDecoration.get(tn);
        if (expressions != null) return;
        if (tn.tmodifiers == null) return;

        for (int i = 0; i < tn.tmodifiers.size(); i++) {
            TypeModifierPragma p = tn.tmodifiers.elementAt(i);

            int tag = p.getTag();
            switch (tag) {
            case TagConstants.ARRAYGUARDMODIFIERPRAGMA:
                // handle later
                break;

            case TagConstants.GENERICARGUMENTPRAGMA:
                if (typeArgumentDecoration.get(tn) != null) {
                    ErrorSet.error(
                        tn.getStartLoc(),
                        "can only have one type argument list for class or interface name.");
                }
                GenericArgumentPragma gp = (GenericArgumentPragma)p;
                typeArgumentDecoration.set(tn, gp.expressions);
                break;
            default:

                Assert.fail("Unexpected tag " + tag);
            }
        }
    }

    /**
     * This method is called by the environment at the end of resolving
     * a type name. At this point <code>sig</code> is what the environment
     * thinks corresponds to <code>tn</code>, and is not <code>null</code>.
     * 
     * We use this hook to select the signature of the instantiation
     * if <code>tn</code> is a type with ghost arguments.
     */
    // @ ensures \result != null;
    public javafe.tc.TypeSig processTypeNameAnnotations(
        /*@non_null*/ TypeName tn, 
        javafe.tc.TypeSig sig, 
        Env env
    ) {
        Info.out("[process type name annotations for " + tn.name.printName()
            + "]");
        processGenericArgumentPragmas(tn);
        ExprVec expressions = (ExprVec)typeArgumentDecoration.get(tn);
        return findTypeSignature(env, sig, expressions, tn.getStartLoc());
    }

    /**
     * Get a (fresh or cached) type instantiation corresponding to
     * <code>sig</code> receiving the arguments <code>expressions</code>.
     * In the process, detect if we don't provide any argument to a template
     * type.
     * 
     * @param env The current environment.
     * @param sig The type to be instantiated.
     * @param expressions The actual type arguments.
     * @param locForError Where to report an error.
     * @return A type instantiation.
     */
    public javafe.tc.TypeSig findTypeSignature(
        Env env,
        javafe.tc.TypeSig sig,
        ExprVec expressions,
        int locForError
    ) {
        if (expressions == null) {
            if (typeParametersDecoration.get(sig) != null) {
                // We have formal parameters but no actual argument.
                ErrorSet.fatal(locForError, "no type arguments given for "
                    + sig.simpleName);
            } else {
                // Not a "generic" type so [sig] is its own instance.
                return sig;
            }
        }

        // Lookup in the cache of existing instantiations or create a new one.
        javafe.tc.TypeSig instantiation = findInstantiation(sig, expressions);
        if (instantiation != null) return instantiation;
        return createInstantiation(env, sig, expressions);
    }

    /**
     * A signature obtained by instantiating <code>sig</code> with
     * <code>expressions</code>. Note that the resulting signature has not
     * been prepped (it lacks information about its methods and fields). A bunch
     * of errors (such as template parameter mismatch) are detected and reported
     * during the process.
     * 
     * @param env The environment in which the instance appears.
     * @param sig The "template" type signature.
     * @param expressions The template arguments.
     * @return A new signature in a new environment pointing to a clone
     *         declaration that has template arguments substituted for the
     *         formal parameters.
     */
    protected javafe.tc.TypeSig createInstantiation(
        Env env,
        javafe.tc.TypeSig sig,
        ExprVec expressions
    ) {
        Info.out("[instantiating " + sig.simpleName + " with "
            + PrettyPrint.inst.toString(expressions) + "]");
        
        return sig; // DBG
        /*

        TypeDecl decl = sig.getTypeDecl();
        TypeSig newSig = TypeSig.instantiate(sig, expressions, env);
        FormalParaDeclVec parameters = (FormalParaDeclVec)PrepTypeDeclaration.typeParametersDecoration.get(sig);
        if (parameters == null) {
            Env currEnv = getEnvForCurrentSig(sig, true);
            checkTypeModifierPragmaVec(decl.tmodifiers, decl, currEnv, sig);
            parameters = (FormalParaDeclVec)PrepTypeDeclaration.typeParametersDecoration.get(sig);
            if (parameters == null) {
                ErrorSet.fatal(
                    decl.getStartLoc(),
                    "no type arguments expected for " + sig.simpleName);
            }
        }
        if (expressions == null) {
            ErrorSet.fatal(decl.getStartLoc(), "no type arguments given for "
                + sig.simpleName);
        }
        if (parameters.size() != expressions.size()) {
            ErrorSet.fatal(
                decl.getStartLoc(),
                "mismatch in number of type arguments for " + sig.simpleName);
        }
        SubstitutionVec subs = SubstitutionVec.make();
        for (int i = 0; i < parameters.size(); i++) {
            Expr expr = expressions.elementAt(i);
            FormalParaDecl parameter = parameters.elementAt(i);

            // Prepare a substitution to replace the ghost parameter
            // with the argument.
            FieldAccess fa = FieldAccess.make(
                ExprObjectDesignator.make(
                    parameter.getStartLoc(),
                    ThisExpr.make(sig, parameter.getStartLoc())),
                parameter.id,
                parameter.getStartLoc());
            AmbiguousVariableAccess aa = AmbiguousVariableAccess.make(
                SimpleName.make(parameter.id, parameter.getStartLoc()));
            subs.addElement(new Substitution(fa, expr));
            subs.addElement(new Substitution(aa, expr));
        }
        
        // Make `this' point to the type instantiation.
        subs.addElement(new Substitution(
            ThisExpr.make(sig, sig.getTypeDecl().getStartLoc()), 
            ThisExpr.make(newSig, sig.getTypeDecl().getStartLoc())));
        MultipleSubstitution ms = new MultipleSubstitution(
            subs, new EqualsASTNoDecl());
        CloneWithSubstitution clone = new CloneForInstantiation(ms);
        decl = (TypeDecl)clone.clone(decl, true);
        newSig.finishInst(decl, sig, expressions);
        instantiations.addElement(new Instantiation(sig, expressions, newSig));
        
        // Fields should have an updated parent.
        for (int i = 0; i < decl.elems.size(); ++i) {
            TypeDeclElem declElem = decl.elems.elementAt(i);
            if (declElem.getParent() != decl)
                System.out.println("oops");
        }

        // An instance does not have any type parameters.
        typeParametersDecoration.set(newSig, null);
        return newSig;
        */
    }

    /**
     * Returns an environment for <code>sig</code>. The information about
     * members is taken from <code>fieldsSeq</code> and from
     * <code>methodsSeq</code>, which were populated by the declaration visit
     * methods.
     * 
     * @param sig The signature for which an environment is requested.
     * @param isStatic The result contains bindings for non-static members iff
     *            <code>isStatic</code>.
     * @return An environment containing all the members of <code>sig</code>.
     */
    protected EnvForTypeSig getEnvForCurrentSig(
        javafe.tc.TypeSig sig,
        boolean isStatic) {
        Env env;

        if (sig.state >= TypeSig.PREPPED) {
            return sig.getEnv(isStatic);
        }
        env = sig.getEnv(isStatic);
        EnvForInstantiation envForCheck = new EnvForInstantiation(
            env,
            sig,
            getFieldsFromStack(),
            getMethodsFromStack(),
            isStatic);
        // DBG: envForCheck.display();
        return envForCheck;
    }

    FieldDeclVec getFieldsFromStack() {
        int sz = fieldSeq.size();
        FieldDecl v[] = new FieldDecl[sz];
        fieldSeq.copyInto(v);
        return FieldDeclVec.make(v);
    }

    MethodDeclVec getMethodsFromStack() {
        int sz = methodSeq.size();
        MethodDecl v[] = new MethodDecl[sz];
        methodSeq.copyInto(v);
        return MethodDeclVec.make(v);
    }

}
