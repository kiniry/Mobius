/* Copyright 2000, 2001, Compaq Computer Corporation */

package escjava.tc;

import javafe.ast.*;
import escjava.ast.TagConstants;

import javafe.tc.*;

import javafe.util.*;

public abstract class Types extends javafe.tc.Types
{
    public static PrimitiveType
            anyType = PrimitiveType.make(TagConstants.ANY, Location.NULL);

    public static PrimitiveType
            typecodeType = PrimitiveType.make(TagConstants.TYPECODE, Location.NULL);

    public static PrimitiveType
            locksetType = PrimitiveType.make(TagConstants.LOCKSET, Location.NULL);

    public static PrimitiveType
	    rangeType = PrimitiveType.make(TagConstants.DOTDOT, Location.NULL);

    /**
     * This routine overrides {@link javafe.tc.Types#lookupField}.  Unlike that
     * routine, it knows about ghost fields and spec_public.
     *
     * <p> This routine assumes we are in an annotation so ghost fields are visible
     * and spec_public is equivalent to public. </a>
     */
    //@ requires t != null
    public static FieldDecl lookupField(Type t, Identifier id, TypeSig caller) 
	    throws LookupException {
	Assert.notNull(t);
	if (t instanceof TypeName)
	    t = TypeSig.getSig((TypeName) t);
	Assert.notNull(t);

	/*
	 * Looking up a field in an arraytype is equivalent to looking
	 * up that field in java.lang.Object unless the field name is
	 * "length":
	 */
	if (t instanceof ArrayType && id != javafe.tc.Types.lenId)
	    t = javaLangObject();

	// Our functionality is different only for TypeSigs:
	if (!(t instanceof TypeSig))
            return javafe.tc.Types.lookupField(t, id, caller);
	TypeSig sig = (TypeSig)t;

	//	/*
	//	 * Extend caller to handle spec_public:
	//	 */
	//	caller = new ExtendedTypeSig(caller);

	// Search for a normal field first; propogate any errors other
	// than NOTFOUND:
	try {
	    return sig.lookupField(id, caller);
	} catch (LookupException E) {
	    if (E.reason != LookupException.NOTFOUND)
		throw E;
	}

	// If not found, search for a ghost field:
	GhostEnv G = new GhostEnv(sig.getEnclosingEnv(), sig, false);
	FieldDecl decl = G.getGhostField(id.toString(), null);
	if (decl==null)
	    throw new LookupException(LookupException.NOTFOUND);

	// Make sure the ghost field is not ambiguous:
	if (G.getGhostField(id.toString(), decl) != null)
	    throw new LookupException(LookupException.AMBIGUOUS);

	// Ghost fields are always public, so no access checking required...

	return decl;
    }
} // end of class Types

/*
 * Local Variables:
 * Mode: Java
 * fill-column: 85
 * End:
 */
