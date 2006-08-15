/* Copyright 2000, 2001, Compaq Computer Corporation */

package rcc.tc;

import rcc.ast.TagConstants;
import java.io.*;
import rcc.ast.EqualsAST;
import rcc.ast.RccPrettyPrint;

import javafe.tc.*;

import javafe.util.*;

import java.io.ByteArrayOutputStream;
import javafe.ast.*;
import javafe.util.ErrorSet;
import javafe.util.Assert;
import javafe.util.Location;

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
    protected javafe.tc.TypeSig makeTypeSigInstance(String[] packageName,
    /* @ non_null @ */String simpleName, javafe.tc.TypeSig enclosingType,
            TypeDecl decl, CompilationUnit CU) {
        return new rcc.tc.TypeSig(packageName, simpleName, enclosingType, decl,
                CU);
    }

    /*
     * protected javafe.tc.TypeSig newTypeSigInstance() { return new
     * rcc.tc.TypeSig(); }
     */
    ExprVec getElemGuard(ArrayType t) {
        return (ExprVec) FlowInsensitiveChecks.getElemGuardedVec(t, null);
    }

    // @ requires x!=null && y!=null
    public boolean isSameTypeInstance(Type x, Type y) {

        if (x instanceof TypeName)
            x = TypeSig.getSig((TypeName) x);
        if (y instanceof TypeName)
            y = TypeSig.getSig((TypeName) y);

        Assert.notFalse(x != null && y != null); // @ nowarn Pre

        if (x.getTag() != y.getTag())
            return false;
        switch (x.getTag()) {
        case TagConstants.ARRAYTYPE:
            return isSameType(((ArrayType) x).elemType,
                    ((ArrayType) y).elemType)
                    && equality.equalsSet(getElemGuard((ArrayType) x),
                            getElemGuard((ArrayType) y)); // @nowarn Cast
        case TagConstants.TYPESIG:
            return x == y;
        default:
            // x and y are the same primitive type
            return true;
        }
    }

    // @ requires s!=null && t!=null
    public boolean isCastableInstance(Type s, Type t) {
        Assert.notNull(s);
        Assert.notNull(t);

        // Replace TypeNames by corresponding TypeSigs

        if (s instanceof TypeName)
            s = TypeSig.getSig((TypeName) s);
        if (t instanceof TypeName)
            t = TypeSig.getSig((TypeName) t);

        Assert.notNull(s); // @ nowarn Pre
        Assert.notNull(t); // @ nowarn Pre

        if (s instanceof PrimitiveType) {
            if (t instanceof PrimitiveType) {
                return javafe.tc.Types.isAnyPrimitiveConvertable(
                        (PrimitiveType) s, (PrimitiveType) t);
            } else if (s.getTag() == TagConstants.NULLTYPE) {
                // a cast from null to a reference type
                return true;
            }
        } else if (s instanceof javafe.tc.TypeSig) {
            javafe.tc.TypeSig sSig = (javafe.tc.TypeSig) s;
            TypeDecl sDecl = sSig.getTypeDecl();
            if (sDecl instanceof ClassDecl) {
                // s is a class

                if (t instanceof javafe.tc.TypeSig) {
                    javafe.tc.TypeSig tSig = (javafe.tc.TypeSig) t;
                    TypeDecl tDecl = tSig.getTypeDecl();
                    if (tDecl instanceof ClassDecl) {
                        // t is a class
                        // must be related classes
                        return tSig.isSubtypeOf(sSig) || sSig.isSubtypeOf(tSig);
                    } else {
                        // t is an interface
                        // Require s is not final, or s implements t
                        return !Modifiers.isFinal(sDecl.modifiers)
                                || sSig.isSubtypeOf(tSig);
                    }
                } else if (t instanceof ArrayType) {
                    // t is an array type, s must be Object
                    return isSameType(sSig, javaLangObject());
                } else {
                    // t is a primitive type, s is a class, so not castable
                    Assert.notFalse(t instanceof PrimitiveType); // @nowarn
                                                                    // Pre
                    return false;
                }
            } else {
                // s is an interface
                if (t instanceof javafe.tc.TypeSig) {
                    javafe.tc.TypeSig tSig = (javafe.tc.TypeSig) t;
                    TypeDecl tDecl = tSig.getTypeDecl();
                    if (tDecl instanceof ClassDecl) {
                        // t is a class
                        // require t is not final, or t implements s
                        return !Modifiers.isFinal(tDecl.modifiers)
                                || tSig.isSubtypeOf(sSig);
                    } else {
                        // t is an interface
                        // is s and t contain methods with the same signature
                        // but
                        // different return types, then an error occurs
                        // TO BE DONE
                        return true;
                    }
                } else {
                    // t is a primitive or array type
                    // MAYBE SHOULD ALLOW CASTING OF CLONEABLE TO ARRAY
                    Assert.notFalse(t instanceof PrimitiveType // @ nowarn Pre
                            || t instanceof ArrayType);
                    return false;
                }
            }
        } else if (s instanceof ArrayType) {
            // s is an array

            Type sElem = ((ArrayType) s).elemType;

            if (t instanceof javafe.tc.TypeSig) {
                // Must be Object or Cloneable
                Type tSig = (javafe.tc.TypeSig) t;
                return isSameType(tSig, javaLangObject())
                        || isSameType(tSig, javaLangCloneable());
            } else if (t instanceof ArrayType) {
                Type tElem = ((ArrayType) t).elemType;

                if (sElem instanceof PrimitiveType
                        && tElem instanceof PrimitiveType) {
                    // require same element type
                    return sElem.getTag() == tElem.getTag()
                            && equality.subset(getElemGuard((ArrayType) s),
                                    getElemGuard((ArrayType) t));
                } else if (!(sElem instanceof PrimitiveType)
                        && !(tElem instanceof PrimitiveType)) {
                    // require elements to be castable
                    return isCastable(sElem, tElem)
                            && equality.subset(getElemGuard((ArrayType) s),
                                    getElemGuard((ArrayType) t));
                } else
                    return false;
            } else {
                Assert.notFalse(t instanceof PrimitiveType); // @ nowarn Pre
                return false;
            }
        }
        // Assert.fail("Fall thru2, s="+printName(s)+" t="+t+printName(t));
        return false;
    }

    // @ requires x!=null && y!=null
    public boolean isInvocationConvertableInstance(Type x, Type y) {
        if (isSameType(x, y))
            return true;
        if (isWideningPrimitiveConvertable(x, y))
            return true;
        if (isWideningReferenceConvertable(x, y))
            return true;
        return false;
    }

    // @ requires s!=null && t!=null
    public boolean isWideningReferenceConvertableInstance(Type s, Type t) {
        if (s instanceof TypeName)
            s = TypeSig.getSig((TypeName) s);
        if (t instanceof TypeName)
            t = TypeSig.getSig((TypeName) t);
        Assert.notNull(s); // @ nowarn Pre
        Assert.notNull(t); // @ nowarn Pre
        if (s instanceof javafe.tc.TypeSig && t instanceof javafe.tc.TypeSig
                && ((javafe.tc.TypeSig) s).isSubtypeOf((javafe.tc.TypeSig) t))
            return true;

        if (s.getTag() == TagConstants.NULLTYPE
                && (t instanceof javafe.tc.TypeSig || t.getTag() == TagConstants.ARRAYTYPE))
            return true;

        if (s.getTag() == TagConstants.ARRAYTYPE) {
            if (t.getTag() == TagConstants.ARRAYTYPE) {
                Type sElem = ((ArrayType) s).elemType; // @ nowarn Cast
                Type tElem = ((ArrayType) t).elemType; // @ nowarn Cast
                return (isSameType(sElem, tElem) || javafe.tc.Types
                        .isWideningReferenceConvertable(sElem, tElem))
                        && equality.subset(getElemGuard((ArrayType) s),
                                getElemGuard((ArrayType) t));
            } else if (Types.isSameType(t, javaLangObject())) {
                return true;
            } else
                return false;
        }
        return false;
    }

    /**
     * Returns the name of a <code>Type</code> as a <code>String</code>.
     * The resulting name will be fully qualified if the <code>Type</code>
     * has been name resolved.
     */
    //@ requires PrettiPrint.inst != null;
    //@ ensures \result != null;
    public String printNameInstance(Type t) {
        if (t instanceof TypeName) {
            javafe.tc.TypeSig sig = TypeSig.getSig((TypeName) t);
            if (sig != null)
                return sig.toString();
        } else if (t instanceof ArrayType) {
            return printName(((ArrayType) t).elemType)
                    + "["
                    + (((ArrayType) t).tmodifiers == null ? ""
                            : (new RccPrettyPrint(javafe.ast.PrettyPrint.inst,
                                    javafe.ast.PrettyPrint.inst))
                                    .toString(((ArrayType) t).tmodifiers))
                    + "]";
        }
        ByteArrayOutputStream result = new ByteArrayOutputStream(20);
        PrettyPrint.inst.print(result, t);
        return result.toString();
    }

    static Identifier lenId = Identifier.intern("length");

    /**
     * This routine replaces <code>javafe.tc.Types.lookupField</code>. 
     * Unlike that routine, it knows about ghost fields and <tt>spec_public</tt>.
     * This routine assumes we are in an annotation so ghost fields are 
     * visible and <tt>spec_public</tt> is equivalent to public.
     * 
     * PRE: We are in an annotation.
     */
    protected FieldDecl lookupFieldInstance(
            /*@ non_null */ Type t, 
            Identifier id,
            javafe.tc.TypeSig caller) 
    throws LookupException {
        Assert.notNull(t);

        if (t instanceof TypeName)
            t = TypeSig.getSig((TypeName) t);

        FieldDecl decl = null;
        Assert.notNull(t);

        if (t instanceof javafe.tc.TypeSig) {
            try {
                decl = ((javafe.tc.TypeSig) t).lookupField(id, caller);
                return decl;
            } catch (LookupException e) {
                if (e.reason != LookupException.NOTFOUND) {
                    throw e;
                }
            }
            if (true) {

                javafe.tc.TypeSig sig = (javafe.tc.TypeSig) t;

                // If not found, search for a ghost field:
                GhostEnv G = new GhostEnv(sig.getEnclosingEnv(), sig, false);

                decl = G.getGhostField(id.toString(), null);

                if (decl == null)
                    throw new LookupException(LookupException.NOTFOUND);

                // Make sure the ghost field is not ambiguous:
                if (G.getGhostField(id.toString(), decl) != null)
                    throw new LookupException(LookupException.AMBIGUOUS);

                // Ghost fields are always public, so no access checking
                // required...
            }
            return decl;
        } else if (t instanceof ArrayType) {
            if (id == lenId)
                return lengthFieldDecl;
            else
                throw new LookupException(LookupException.NOTFOUND);
        } else if (t instanceof PrimitiveType) {
            throw new LookupException(LookupException.NOTFOUND);
        } else {
            Assert.fail("Unexpected type " + t.getTag());
            return null;
        }

    }
}
