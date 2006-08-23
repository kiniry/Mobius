/* Copyright 2000, 2001, Compaq Computer Corporation */

package rcc.tc;

import javafe.ast.ASTDecoration;
import javafe.ast.ClassDecl;
import javafe.ast.CompilationUnit;
import javafe.ast.ExprVec;
import javafe.ast.FieldDeclVec;
import javafe.ast.MethodDeclVec;
import javafe.ast.Name;
import javafe.ast.PrettyPrint;
import javafe.ast.TypeDecl;
import javafe.ast.TypeName;
import javafe.tc.CheckCompilationUnit;
import javafe.tc.Env;
import javafe.tc.SLResolution;
import javafe.util.Assert;
import javafe.util.Info;

/**
 * Creates default instances.
 * 
 * @see javafe.tc.TypeSig
 */
// TODO: Why are default instances needed?
public class TypeSig extends javafe.tc.TypeSig {

    // for recover instantiation info from instance of it.
    public ExprVec expressions; // do not set outside of finishInst

    public javafe.tc.TypeSig generic; // do not set outside of finishInst

    public static final ASTDecoration defaultInstantiationDecoration = new ASTDecoration(
        "default instantiation");

    /**
     * {@inheritDoc} Also remember the enclosing type.
     * 
     * @param enclosingType The enclosing type.
     */
    public TypeSig(String[] packageName,
    /* @ non_null @ */String simpleName, javafe.tc.TypeSig enclosingType,
        TypeDecl decl, CompilationUnit CU) {

        super(packageName, simpleName, decl, CU);

        member = true;
        this.enclosingType = enclosingType;

        this.enclosingEnv = null; // be lazy...
        if (decl != null) setDecl(decl, CU);
    }

    public TypeSig(String simpleName,
    /* @ non_null @ */Env enclosingEnv,
    /* @ non_null @ */TypeDecl decl) {
        super(simpleName, enclosingEnv, decl);
    }

    public void resolveSupertypeLinks() {
        if (state >= LINKSRESOLVED) return;

        if (((rcc.tc.PrepTypeDeclaration)PrepTypeDeclaration.getInst()).hasParameters(this)) {
            Info.out("[super class resolving class " + this + " to be Object]");

            CheckCompilationUnit.checkCompilationUnit(getCompilationUnit());
            TypeDecl d = getTypeDecl();
            for (int i = 0; i < d.superInterfaces.size(); i++)
                SLResolution.handleSuperTypeName(
                    this,
                    d.superInterfaces.elementAt(i));

            if (getTypeDecl() instanceof ClassDecl) {
                ClassDecl cd = (ClassDecl)getTypeDecl();
                cd.superClass = TypeName.make(null, Name.make(
                    "java.lang.Object",
                    cd.locOpenBrace));
                TypeSig.setSig(cd.superClass, Types.javaLangObject());
            }
            state = LINKSRESOLVED;
            return;
        }
        javafe.tc.SLResolution.transition(this);
    }

    /**
     * {@inheritDoc}
     * If there are any parameters then typecheck the default 
     * instantiation of <code>this</code>.
     */
    public void typecheck() {
        if (this.state >= TypeSig.CHECKED) return;
        if (this.state < TypeSig.PREPPED) prep();

        Info.out("[typechecking " + this + "]");
        if (((rcc.tc.PrepTypeDeclaration)rcc.tc.PrepTypeDeclaration.getInst()).hasParameters(this)) {
            Info.out("[creating default instantiation for " + this + "]");
            TypeSig defaultInst = FlowInsensitiveChecks.defaultInstantiation(this);
            defaultInst.state = PARSED;
            defaultInst.prep();
            TypeCheck.inst.makeFlowInsensitiveChecks().checkTypeDeclaration(
                defaultInst);
            defaultInst.state = CHECKED;
            defaultInstantiationDecoration.set(this, defaultInst);
        } else {
            TypeCheck.inst.makeFlowInsensitiveChecks().checkTypeDeclaration(
                this);
        }
        this.state = TypeSig.CHECKED;
    }

    static final public ASTDecoration prepPartDecoration = new ASTDecoration(
        "prep");

    // @ ensures RES!=null
    public FieldDeclVec getFields() {
        PrepPart p = (PrepPart)prepPartDecoration.get(this);
        if (p == null) {
            prep();
            Assert.notNull(fields); // @ nowarn Pre
            return fields;
        } else {
            return p.fields;
        }
    }

    /** Similar to <code>getFields</code>, except for methods. */
    // @ ensures RES!=null
    public MethodDeclVec getMethods() {
        PrepPart p = (PrepPart)prepPartDecoration.get(this);
        if (p == null) {
            prep();
            Assert.notNull(methods); // @ nowarn Pre
            return methods;
        } else {
            return p.methods;
        }
    }

    /**
     * Makes a shallow copy of a type signature. Does not copy the method and
     * field lists. The simple name of the resulting signature will be
     * <tt>oldname&lt;expressions&gt;</tt>.
     * 
     * @param t The type signature to copy.
     * @param expressions Used to construct the simple name of the result.
     * @param env The environment of the result.
     * @return A type signature: <code>t</code> with the modifications
     *         described above
     */
    static public rcc.tc.TypeSig instantiate(
        javafe.tc.TypeSig t,
        ExprVec expressions,
        Env env) {
        rcc.tc.TypeSig sig = new rcc.tc.TypeSig(
            t.packageName,
            t.simpleName,
            t.enclosingType,
            null,
            t.getCompilationUnit());

        sig.packageName = t.packageName;
        sig.enclosingType = t.enclosingType;
        sig.member = t.member;
        sig.simpleName = t.simpleName;
        sig.CU = t.getCompilationUnit();
        sig.fields = null;
        sig.methods = null;
        sig.state = TypeSig.PARSED;
        sig.enclosingEnv = env;

        sig.simpleName = sig.simpleName + "<"
            + PrettyPrint.inst.toString(expressions) + ">";

        return sig;
    }

    public void finishInst(TypeDecl d, javafe.tc.TypeSig sig, ExprVec exprs) {
        this.expressions = exprs;
        this.generic = sig;

        // Assert(((rcc.tc.TypeSig)sig).generic == null);

        super.setDecl(d, CU);
    }

}
