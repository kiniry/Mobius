/* Copyright 2000, 2001, Compaq Computer Corporation */

package rcc.tc;

// NOTE do NOT import javafe.tc.TypeSig

import javafe.ast.ArrayType;
import javafe.ast.CompilationUnit;
import javafe.ast.ExprVec;
import javafe.ast.FieldDecl;
import javafe.ast.Identifier;
import javafe.ast.PrettyPrint;
import javafe.ast.Type;
import javafe.ast.TypeDecl;
import javafe.ast.TypeName;
import javafe.tc.Env;
import javafe.tc.LookupException;
import javafe.util.Assert;
import rcc.Dbg;
import rcc.ast.EqualsAST;
import rcc.ast.RccPrettyPrint;
import rcc.tc.TypeSig;

/**
 * The responsabilities of this class include: - look at the array element
 * guards when checking for compatibility - print the elem guards when an array
 * type is printed - make sure the front-end uses the RCC TypeSig-s - also
 * lookup in ghost fields We override the following to handle array types: -
 * isCastableInstance - isSameTypeInstance -
 * isWideningReferenceConvertableInstance - printNameInstance (BEWARE:
 * `instance' here refers to instances of the rcc.tc.Types class) We override
 * the following factory method to use RCC TypeSig-s: - makeTypeSigInstance We
 * override the following method to also lookup ghost fields. -
 * lookupFieldInstance
 */
public class Types extends javafe.tc.Types {
    EqualsAST equality = new EqualsAST();

    static {
        inst = new rcc.tc.Types();
    }

    protected javafe.tc.TypeSig newTypeSigInstance(
        String simpleName,
        /*@non_null*/Env enclosingEnv,
        /*@non_null*/TypeDecl decl
    ) {
        return new rcc.tc.TypeSig(simpleName, enclosingEnv, decl);
    }
    
    protected javafe.tc.TypeSig makeDummyTypeSigInstance() {
        return new TypeSig();
    }

    protected javafe.tc.TypeSig makeTypeSigInstance(
        String simpleName,
        Env enclosingEnv,
        TypeDecl decl
    ) {
        return new TypeSig(simpleName, enclosingEnv, decl);
    }

    protected javafe.tc.TypeSig makeTypeSigInstance(
        String[] packageName,
        String simpleName, 
        javafe.tc.TypeSig enclosingType,
        TypeDecl decl, 
        CompilationUnit CU
    ) {
        return new TypeSig(
            packageName,
            simpleName,
            (TypeSig)enclosingType,
            decl,
            CU);
    }

    /*
     * protected javafe.tc.TypeSig newTypeSigInstance() { return new
     * rcc.tc.TypeSig(); }
     */
    ExprVec getElemGuard(ArrayType t) {
        return FlowInsensitiveChecks.getElemGuardedVec(t, null);
    }

    /**
     * If normal checks succeed:
     *   a. if it is an array then look at elem guard,
     *   b. if it they are TypeSig-s then compare them.
     */
    // @ requires x!=null && y!=null
    public boolean isSameTypeInstance(Type x, Type y) {
        boolean r = super.isSameTypeInstance(x, y);
        if (!r) return false;
        if (x instanceof ArrayType) {
            ExprVec gx = getElemGuard((ArrayType)x);
            ExprVec gy = getElemGuard((ArrayType)y);
            return equality.equalsSet(gx, gy);
        }
        return true;
    }

    protected boolean isWideningReferenceConvertableInstance(Type x, Type y) {
        boolean r = super.isWideningReferenceConvertableInstance(x, y);
        if (!r) return false;
        if (x instanceof ArrayType && y instanceof ArrayType) {
            ExprVec gx = getElemGuard((ArrayType)x);
            ExprVec gy = getElemGuard((ArrayType)y);
            return equality.subset(gx, gy);
        }
        return true;
    }

    // @ requires s!=null && t!=null
    public boolean isCastableInstance(Type s, Type t) {
        if (s instanceof TypeName) s = TypeSig.getSig((TypeName)s);
        if (t instanceof TypeName) t = TypeSig.getSig((TypeName)t);
        return super.isCastableInstance(s, t);
    }

    /**
     * Returns the name of a <code>Type</code> as a <code>String</code>.
     * The resulting name will be fully qualified if the <code>Type</code> has
     * been name resolved. TODO this is an ugly hack and should be fixed
     */
    // @ ensures \result != null;
    public String printNameInstance(Type t) {
        if (t instanceof ArrayType) {
            ArrayType at = (ArrayType)t;
            RccPrettyPrint rpp = (RccPrettyPrint)PrettyPrint.inst;
            return printName(at.elemType) + "[" + rpp.toString(at.tmodifiers)
                + "]";
        }
        return super.printNameInstance(t);
    }

    /**
     * This routine replaces <code>javafe.tc.Types.lookupField</code>. Unlike
     * that routine, it knows about ghost fields and <tt>spec_public</tt>.
     * This routine assumes we are in an annotation so ghost fields are visible
     * and <tt>spec_public</tt> is equivalent to public. PRE: We are in an
     * annotation.
     */
    protected FieldDecl lookupFieldInstance(
        /*@non_null*/ Type t, 
        Identifier id, 
        javafe.tc.TypeSig caller
    ) throws LookupException {
        Dbg.o("lookup " + id + " in", t);
        FieldDecl decl = null;
        try {
            decl = super.lookupFieldInstance(t, id, caller);
        }
        catch (LookupException e) {
            Dbg.o("looking at ghost fields for " + id);
            if (e.reason != LookupException.NOTFOUND || !(t instanceof TypeSig)) throw e;

            // Try to also look in the ghost fields of |t|
            TypeSig sig = (TypeSig)t;
            decl = sig.getFormal(id.toString());
            if (decl == null) throw e; // still not found
        }
        Assert.notFalse(!(decl.type instanceof TypeSig) || !((TypeSig)decl.type).isInstance());
        Dbg.o(decl.type.getClass().getName());
        Dbg.o("found " + id + " and it's fine");
        return decl;
    }
}
