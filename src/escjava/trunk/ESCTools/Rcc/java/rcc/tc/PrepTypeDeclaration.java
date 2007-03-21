/* Copyright 2000, 2001, Compaq Computer Corporation */

package rcc.tc;

import javafe.ast.ASTDecoration;
import javafe.ast.ASTNode;
import javafe.ast.ClassDecl;
import javafe.ast.ExprVec;
import javafe.ast.FieldDecl;
import javafe.ast.FormalParaDecl;
import javafe.ast.InterfaceDecl;
import javafe.ast.ModifierPragma;
import javafe.ast.ModifierPragmaVec;
import javafe.ast.Modifiers;
import javafe.ast.TypeDecl;
import javafe.ast.TypeDeclElem;
import javafe.ast.TypeModifierPragma;
import javafe.ast.TypeModifierPragmaVec;
import javafe.ast.TypeName;
import javafe.tc.Env;
import javafe.util.Assert;
import javafe.util.ErrorSet;
import javafe.util.Info;
import javafe.util.Location;
import rcc.Dbg;
import rcc.ast.CloneAST;
import rcc.ast.GenericArgumentPragma;
import rcc.ast.GenericParameterPragma;
import rcc.ast.TagConstants;

/**
 * TODO Some of the Dbg.o calls should perhaps be transformed into Info.out
 *      when I finish packaging RCC.
 * 
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
 * AST decorations and we create TypeSig instantiations. (So it handles
 * the places where you give arguments to types.)
 *  - processTypeNameAnnotations
 *
 * We override the following methods to process generic parameters into
 * field declarations added as decorations to the type declaration.
 *  - visitClassDecl
 *  - visitInterfaceDecl
 *  (NOTE that the actual work is done in checkTYpeModifierPragma)  
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

    /**
     * This decoration is put on <code>TypeName</code>-s and holds the
     * ghost argument expression list.
     */
    static public final ASTDecoration typeArgumentDecoration 
        = new ASTDecoration("type args");

    public PrepTypeDeclaration() {
        inst = this;
    } // @ nowarn Invariant

    /**
     * Look at all field declarations in type {@code d} and clone
     * their pragma modifiers. Conceptually, the code 
     * {@code A x,y guarded_by l;} is transformed into
     * {@code A x guarded_by l; A y guarded_by l;}.
     */
    private void cloneGuardedBy(TypeDecl d) {
        // clone because pragmas may be shared between fields, ie Foo f,g,h;
        CloneAST clone = new CloneAST();
        for (int i = 0, sz = d.elems.size(); i < sz; i++) {
            TypeDeclElem e = d.elems.elementAt(i);
            if (e instanceof FieldDecl) {
                FieldDecl fd = (FieldDecl)e;
                if (fd.pmodifiers == null) 
                    fd.pmodifiers = ModifierPragmaVec.make();
                ModifierPragma t[] = fd.pmodifiers.toArray();
                for (int j = 0; j < t.length; j++) {
                    t[j] = (ModifierPragma)clone.clone(t[j], true);
                }
                fd.pmodifiers = ModifierPragmaVec.make(t);
            }
        }
    }

    /**
     * TODO comment this!
     */
    // @ requires decl!=null && currentSig!=null
    public void visitClassDecl(ClassDecl decl, javafe.tc.TypeSig currentSig) {
        cloneGuardedBy(decl);
        checkTypeModifierPragmaVec(
            decl.tmodifiers, 
            decl, 
            currentSig);
        super.visitClassDecl(decl, currentSig);
    }

    // @ requires decl!=null && currentSig!=null
    public void visitInterfaceDecl(
        InterfaceDecl decl,
        javafe.tc.TypeSig currentSig
    ) {
        cloneGuardedBy(decl);
        checkTypeModifierPragmaVec(
            decl.tmodifiers, 
            decl, 
            currentSig);
        super.visitInterfaceDecl(decl, currentSig);
    }

    // @ requires env!=null
    protected void checkTypeModifierPragmaVec(
        TypeModifierPragmaVec v,
        ASTNode ctxt,
        javafe.tc.TypeSig currentSig
    ) {
        if (v != null) for (int i = 0; i < v.size(); i++)
            checkTypeModifierPragma(v.elementAt(i), ctxt, currentSig);
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
        javafe.tc.TypeSig currentSig
    ) {
        TypeSig sig = (TypeSig)currentSig;
        int tag = p.getTag();
        switch (tag) {
        case TagConstants.GENERICPARAMETERPRAGMA: {
            GenericParameterPragma pp = (GenericParameterPragma)p;
            if (sig.hasFormals()) {
                // TODO warning for more than one list?
            }
            
            sig.resetFormals();
            for (int i = 0; i < pp.args.size(); i++) {
                FormalParaDecl parameter = pp.args.elementAt(i);
                FieldDecl decl = FieldDecl.make(
                    parameter.modifiers | Modifiers.ACC_FINAL,
                    parameter.pmodifiers,
                    parameter.id,
                    parameter.type,
                    parameter.locId,
                    null,
                    Location.NULL);
                decl.setParent((TypeDecl)ctxt);
                sig.addFormal(decl);
                
                // TODO make sure these are Objects ?
                
                // This attaches a TypeSig to the 'Object' TypeName
                // (and FlowInsensitiveChecks assumes the signature is set
                // for all TypeName-s)
                Env env = getEnvForCurrentSig(currentSig, true);
                env.resolveType(currentSig, decl.type);
            }
            break;
        }
        default:
            Assert.fail("Unexpected tag " + tag);
        }
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
                Dbg.o("I'm moving a GENERICARGUMENTPRAGMA into typeArgumentDecoration", gp.expressions);
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
        Info.out("[process type name annotations for " + tn.name.printName() + "]");
        Dbg.o("I'm processing type annotations of " + tn.name.printName());
        processGenericArgumentPragmas(tn);
        return sig;
    }

}
