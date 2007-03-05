/* Copyright 2000, 2001, Compaq Computer Corporation */

package rcc.tc;

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
import rcc.ast.EqualsAST;
import rcc.ast.RccPrettyPrint;
import rcc.ast.TagConstants;

/**
 * The responsabilities of this class include:
 *  - look at the array element guards when checking for compatibility
 *  - print the elem guards when an array type is printed
 *  - make sure the front-end uses the RCC TypeSig-s
 *  - also lookup in ghost fields
 * 
 * We override the following to handle array types:
 *  - isCastableInstance
 *  - isSameTypeInstance
 *  - printNameInstance 
 * 
 * We override the following factory method to use RCC TypeSig-s:
 *  - makeTypeSigInstance
 * 
 * We override the following method to also lookup ghost fields.
 *  - lookupFieldInstance
 */
public class Types extends javafe.tc.Types {
    EqualsAST equality = new EqualsAST();

    static {
        inst = new rcc.tc.Types();
    }

    protected javafe.tc.TypeSig newTypeSigInstance(String simpleName,
    /* @ non_null @ */Env enclosingEnv,
    /* @ non_null @ */TypeDecl decl) {
        return new rcc.tc.TypeSig(simpleName, enclosingEnv, decl);
    }

    // @ requires \nonnullelements(packageName)
    // @ requires (enclosingType!=null) ==> (decl!=null)
    // @ requires (decl==null) == (CU==null)
    // @ ensures \result!=null
    protected javafe.tc.TypeSig makeTypeSigInstance(
        String[] packageName,
        /* @ non_null @ */String simpleName,
        javafe.tc.TypeSig enclosingType,
        TypeDecl decl,
        CompilationUnit CU
    ) {
        return new rcc.tc.TypeSig(
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
     * If normal checks succseed and it is an array, then we also check
     * the elem guard sets (for equality).
     */
    // @ requires x!=null && y!=null
    public boolean isSameTypeInstance(Type x, Type y) {
        boolean r = super.isSameTypeInstance(x, y);
        if (!r) return false;

        if (x.getTag() == TagConstants.ARRAYTYPE) {
            ArrayType ax = (ArrayType)x;
            ArrayType ay = (ArrayType)y;
            return equality.equalsSet(getElemGuard(ax), getElemGuard(ay));
        }
        return true;
    }

    // @ requires s!=null && t!=null
    public boolean isCastableInstance(Type s, Type t) {
        if (s instanceof TypeName) s = TypeSig.getSig((TypeName) s);
        if (t instanceof TypeName) t = TypeSig.getSig((TypeName) t);
        return super.isCastableInstance(s, t);
    }

    /**
     * Returns the name of a <code>Type</code> as a <code>String</code>.
     * The resulting name will be fully qualified if the <code>Type</code> has
     * been name resolved.
     * 
     * TODO this is an ugly hack and should be fixed
     */
    // @ requires PrettiPrint.inst != null;
    // @ ensures \result != null;
    public String printNameInstance(Type t) {
        if (t instanceof ArrayType) {
            ArrayType at = (ArrayType)t;
            RccPrettyPrint rpp = (RccPrettyPrint)PrettyPrint.inst;
            return printName(at.elemType) 
                + "[" + rpp.toString(at.tmodifiers) + "]";
        }
        return super.printNameInstance(t);
    }

    /**
     * This routine replaces <code>javafe.tc.Types.lookupField</code>. Unlike
     * that routine, it knows about ghost fields and <tt>spec_public</tt>.
     * This routine assumes we are in an annotation so ghost fields are visible
     * and <tt>spec_public</tt> is equivalent to public. 
     * PRE: We are in an annotation.
     */
    protected FieldDecl lookupFieldInstance(
        /*@non_null*/ Type t, 
        Identifier id, 
        javafe.tc.TypeSig caller
    ) throws LookupException {
        FieldDecl decl = null;
        try {
            decl = super.lookupFieldInstance(t, id, caller);
        } catch (LookupException e) {
            if (e.reason != LookupException.NOTFOUND || !(t instanceof TypeSig))
                throw e;
            
            // Try to also look in the ghost fields of |t|
            TypeSig sig = (TypeSig)t;
            decl = sig.getFormal(id.toString()); 
            if (decl == null) throw e; // still not found
        }
        return decl;
    }
}
