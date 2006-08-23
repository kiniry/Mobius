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
 * NOTE: According to the documentation of <code>javafe.tc.TypeSig</code> this
 * class, which is responsible of typechecking at signature level, meaning that
 * it does not look at fields of types. In order to avoid call cycles it shoud
 * never use functions from <code>FlowInsensitiveChecks</code> which takes
 * care of the last phases of typechecking.
 */
public class PrepTypeDeclaration extends javafe.tc.PrepTypeDeclaration {

    public PrepTypeDeclaration() {
        inst = this;
    } // @ nowarn Invariant

    // TODO: rewrite this to not clone on every iteration.
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
        checkTypeModifierPragmaVec(decl.tmodifiers, decl, getEnvForCurrentSig(
            s,
            true), s);
    }

    // @ requires decl!=null && currentSig!=null
    public void visitClassDecl(ClassDecl decl, javafe.tc.TypeSig currentSig) {
        // NOTE: This is the only section that differs from superclass
        // Check that the modifiers are ok
        if (!hasParameters(currentSig)) {
            addClassGuardsToFields(decl);
        }
        checkTypeModifiers(decl, currentSig, true);
        checkTypeModifierPragmaVec(decl.tmodifiers, decl, getEnvForCurrentSig(
            currentSig,
            true), currentSig);

        // Visit all enclosed member declarations
        // They will add themselves to fieldSeq and methodSeq
        for (int i = 0; i < decl.elems.size(); i++) {
            visitTypeDeclElem(
                decl.elems.elementAt(i),
                currentSig,
                Modifiers.isAbstract(decl.modifiers),
                Modifiers.isFinal(decl.modifiers),
                false);
        }

        // Add members of direct superclass, if any
        // superclass may be null, or may name an interface
        TypeName superClassName = decl.superClass;
        javafe.tc.TypeSig superClassSig = superClassName == null ? null
            : TypeSig.getSig(superClassName);

        if (superClassSig != null) {
            if (superClassSig.getTypeDecl() instanceof ClassDecl) {
                // check superclass is not final
                if (Modifiers.isFinal(superClassSig.getTypeDecl().modifiers)) {
                    ErrorSet.error(
                        superClassName.getStartLoc(),
                        "Can't subclass final classes: class "
                            + superClassSig.getExternalName());
                } else {
                    addInheritedMembers(currentSig, superClassSig);
                }
                checkSuperTypeAccessible(
                    currentSig,
                    superClassSig,
                    superClassName == null ? decl.getStartLoc()
                        : superClassName.getStartLoc());
            } else {
                ErrorSet.error(
                    superClassName.getStartLoc(),
                    "Can't subclass interfaces: interface "
                        + superClassSig.getExternalName());
            }
        }

        // Add members of direct super interfaces
        checkSuperInterfaces(currentSig, decl.superInterfaces);

        // Check no two abstract methods with same method signature
        // and different return types
        for (int i = 0; i < methodSeq.size(); i++) {
            MethodDecl mdi = (MethodDecl)methodSeq.elementAt(i);
            for (int j = 0; j < i; j++) {
                MethodDecl mdj = (MethodDecl)methodSeq.elementAt(j);

                // Check if mdi and mdj are abstract methods
                // with same signature and different return types
                if (Modifiers.isAbstract(mdi.modifiers)
                    && Modifiers.isAbstract(mdj.modifiers)
                    && Types.isSameMethodSig(mdi, mdj)
                    && !Types.isSameType(mdi.returnType, mdj.returnType)) {
                    ErrorSet.error(decl.loc, "Class " + decl.id
                        + " contains two abstract methods"
                        + " with same signature"
                        + " but different return types");
                }
            }
        }
        // All done
    }

    // @ requires decl!=null && currentSig!=null
    public void visitInterfaceDecl(
        InterfaceDecl decl,
        javafe.tc.TypeSig currentSig) {

        addClassGuardsToFields(decl);
        // Check that the modifiers are ok
        checkTypeModifiers(decl, currentSig, false);
        checkTypeModifierPragmaVec(decl.tmodifiers, decl, getEnvForCurrentSig(
            currentSig,
            true), currentSig);

        // Visit all enclosed member declarations
        // They will add themselves to fieldSeq and methodSeq
        for (int i = 0; i < decl.elems.size(); i++)
            visitTypeDeclElem(
                decl.elems.elementAt(i),
                currentSig,
                true,
                false,
                true);

        checkSuperInterfaces(currentSig, decl.superInterfaces);

        // interfaces inherit members from java.lang.Object
        addInheritedMembers(currentSig, Types.javaLangObject());

        // ### STILL NEED TO CHECK NO DUPLICATE METHOD SIGNATURES ???
        // All done
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
        javafe.tc.TypeSig currentSig) {
        if (v != null) for (int i = 0; i < v.size(); i++)
            checkTypeModifierPragma(v.elementAt(i), ctxt, env, currentSig);
    }

    /**
     * Transforms ghost annotations into field declarations and wraps them in
     * <code>GhostDeclPragma</code> nodes.
     */
    // @ requires p!=null && env!=null
    protected void checkTypeModifierPragma(
        TypeModifierPragma p,
        ASTNode ctxt,
        Env env,
        javafe.tc.TypeSig currentSig) {
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

    static protected EqualsAST equality = new EqualsAST();

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
        ExprVec expressions) {
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

    // TODO: Comment this!
    // @ ensures \result != null;
    public javafe.tc.TypeSig processTypeNameAnnotations(
    /* @ non_null @ */TypeName tn, javafe.tc.TypeSig sig, Env env) {
        Info.out("[process type name annotations for " + tn.name.printName()
            + "]");
        if (env.getEnclosingClass() == null) {
            // TODO: What is this mess?
            // TODO: "_dummy" should be a constant, which also can't be produced
            // by parser
            InterfaceDecl dummy = InterfaceDecl.make(
                0,
                null,
                Identifier.intern("_dummy"),
                TypeNameVec.make(),
                null,
                TypeDeclElemVec.make(),
                Location.NULL,
                Location.NULL,
                Location.NULL,
                Location.NULL);
            env = new EnvForCU(sig.getCompilationUnit());
            rcc.tc.TypeSig s = new rcc.tc.TypeSig(
                sig.packageName,
                "_dummy",
                sig,
                dummy,
                sig.getCompilationUnit());

            env = s.getEnclosingEnv();
        }

        processGenericArgumentPragmas(tn);
        ExprVec expressions = (ExprVec)typeArgumentDecoration.get(tn);
        return findTypeSignature(env, sig, expressions, tn.getStartLoc());
    }

    /**
     * Get a (fresh or cached) type instantiation corresponding to
     * <code>sig</code> receiving the arguments <code>expressions</code>.
     * In the process, detect if we don't provide any argument to a templete
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
        int locForError) {
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
        ExprVec expressions) {
        Info.out("[instantiating " + sig.simpleName + " with "
            + PrettyPrint.inst.toString(expressions) + "]");

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
            subs.addElement(new Substitution(fa, expr));
            subs.addElement(new Substitution(
                AmbiguousVariableAccess.make(SimpleName.make(
                    parameter.id,
                    parameter.getStartLoc())),
                expr));

        }
        // Make `this' point to the type instantiation.
        subs.addElement(new Substitution(ThisExpr.make(
            sig,
            sig.getTypeDecl().getStartLoc()), ThisExpr.make(
            newSig,
            sig.getTypeDecl().getStartLoc())));
        MultipleSubstitution ms = new MultipleSubstitution(
            subs,
            new EqualsASTNoDecl());
        CloneWithSubstitution clone = new CloneForInstantiation(ms);
        decl = (TypeDecl)clone.clone(decl, true);
        newSig.finishInst(decl, sig, expressions);
        instantiations.addElement(new Instantiation(sig, expressions, newSig));

        // An instance does not have any type parameters.
        typeParametersDecoration.set(newSig, null);
        return newSig;
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
