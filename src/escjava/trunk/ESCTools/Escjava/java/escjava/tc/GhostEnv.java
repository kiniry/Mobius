/* Copyright 2000, 2001, Compaq Computer Corporation */

package escjava.tc;

import java.util.Enumeration;
import java.util.Hashtable;

import javafe.ast.*;
import escjava.ast.GhostDeclPragma;
import escjava.ast.ModelDeclPragma;
import escjava.ast.TagConstants;
import escjava.ast.Utils;

import javafe.tc.*;
import javafe.tc.TypeSig;

/**
 * This class overrides {@link EnvForTypeSig} so that it "sees" ghost and model
 * fields if {@link escjava.tc.FlowInsensitiveChecks#inAnnotation} is
 * <code>true</code>.
 */

public class GhostEnv extends EnvForTypeSig
{
    // Creation

    public GhostEnv(/*@ non_null */ Env parent,
		    /*@ non_null */ TypeSig peer,
		    boolean staticContext) {
	super(parent, peer, staticContext);
    }

    // Current/enclosing instances

    /**
     * Returns a new {@link Env} that acts the same as us, except that its current
     * instance (if any) is not accessible.
     *
     * @note This routine is somewhat inefficient and should be avoided unless an
     * unknown environment needs to be coerced in this way.
     */
    public Env asStaticContext() {
	return new GhostEnv(parent, peer, true);
    }

    // Debugging functions

    /**
     * Display information about an {@link Env} to {@link System#out}.  This function
     * is intended only for debugging use.
     */
    public void display() {
	parent.display();
	System.out.println("[[ extended with the (ghost) "
			   + (staticContext ? "static" : "complete")
			   + " bindings of type "
	    + peer.getExternalName() + " ]]");
	FieldDeclVec fdv = ((escjava.tc.TypeSig)peer).jmlFields;
	for (int i=0; i<fdv.size(); ++i) {
		System.out.println("    " + fdv.elementAt(i).id);
	}
	
    }

    // Code to locate our ghost fields by name

    /**
     * Attempts to find a ghost field that belongs to us (including supertypes) with
     * name <code>n</code> that is not equal to <code>excluded</code>, which may be
     * <code>null</code>.
     *
     * @param n the name of the ghost field to get.
     * @param excluded a field declaration to avoid.
     * @return the ghost field declaration if successful, otherwise
     * <code>null</code>.
     */
    public FieldDecl getGhostField(String n, FieldDecl excluded) {
	FieldDeclVec fdv = peer.getFields(false);
	for (int i=0; i<fdv.size(); ++i) {
	    FieldDecl f = fdv.elementAt(i);
	    if (!f.id.toString().equals(n))
		continue;

	    if (f != excluded)
		return f;
	}	

	return null;
    }

    // Code to collect all our ghost fields

//    private Hashtable fields;	// used like a set

    /**
     * Add all new ghost fields found in <code>s</code>.  Also preps them (just resolves their types if
     * needed).
     */
// FIXME - this gets called a great many times
    //private void collectGhostFields(TypeSig s, boolean superclass) {
	// Iterate over all TypeDeclElems in s:
/*
	TypeDecl d = s.getTypeDecl();
	TypeDeclElemVec elems = d.elems;
	for (int i = 0; i < elems.size(); i++) {
	    TypeDeclElem elem = elems.elementAt(i);
	    FieldDecl fd;
	    if (elem instanceof GhostDeclPragma) {
		fd = ((GhostDeclPragma)elem).decl;
	    } else if (elem instanceof ModelDeclPragma) {
		fd = ((ModelDeclPragma)elem).decl;
	    } else if (superclass && (elem instanceof FieldDecl)) {
		fd = (FieldDecl)elem;
		if (Modifiers.isPrivate(fd.modifiers) ||
		    Modifiers.isPackage(fd.modifiers)) {
			if (!(Utils.findModifierPragma(fd.pmodifiers,
				TagConstants.SPEC_PUBLIC) != null ||
			    Utils.findModifierPragma(fd.pmodifiers,
				TagConstants.SPEC_PROTECTED) != null)) continue;
		}
	    } else continue;

	    boolean isStatic = isStatic(fd);
	    if ((isStatic || !staticContext) &&
			    !fields.containsKey(fd)) {
		s.getEnclosingEnv().resolveType(null, fd.type); // FIXME _ use a caller?
		fields.put(fd, fd);
	    }
	}

	// Now recursive to all supertypes:
	if (d instanceof ClassDecl) {
	    TypeName superClass = ((ClassDecl)d).superClass;
	    if (superClass != null)
		collectGhostFields(TypeSig.getSig(superClass),true);
	} else if (d instanceof InterfaceDecl)
	    collectGhostFields(Types.javaLangObject(),true);

	for (int i = 0; i < d.superInterfaces.size(); i++)
	    collectGhostFields(TypeSig.getSig(
		d.superInterfaces.elementAt(i)),true);
*/
    //}

    static public boolean isStatic(FieldDecl d) {
	boolean isStatic = d.parent instanceof InterfaceDecl;
	if (Modifiers.isStatic(d.modifiers)) isStatic = true;
	if (Utils.findModifierPragma(d,
		TagConstants.INSTANCE) != null) isStatic = false;
	return isStatic;
    }

    /**
     * @return all our ghost fields (including our supertypes) as
     * "set" encoded in a hashtable.
     */
/*
    private Hashtable collectGhostFields() {
	if (fields != null)
	    return fields;

	fields = new Hashtable(5);
	collectGhostFields(peer,false);
	return fields;
    }
*/

    // Misc. routines

    /**
     * @return a flag that indicates if the FieldDecl <code>field</code> a ghost
     * field.
     *
     * @note The current implementation of this is slow.  If you need to
     * call this routine a lot, rewrite it so it runs faster.
     */
    public static boolean isGhostField(FieldDecl field) {
	TypeDecl d = field.getParent();
        // special fields like "length" can't be ghost fields
	if (d == null)
	    return false;

	TypeDeclElemVec elems = d.elems;
	for (int i = 0; i < elems.size(); i++) {
	    TypeDeclElem elem = elems.elementAt(i);
	    if (elem instanceof GhostDeclPragma) {
		FieldDecl ghost = ((GhostDeclPragma)elem).decl;
		if (field == ghost)
		    return true;
	    }
	}

	return false;
    }

    /**
     * Override to make ghost fields visible if {@link
     * escjava.tc.FlowInsensitiveChecks#inAnnotation} is <code>true</code>.
     */
    protected boolean hasField(Identifier id) {
	if (peer.hasField(id))
	    return true;

	if (!FlowInsensitiveChecks.inAnnotation)
	    return false;

	return (getGhostField(id.toString(), null) != null);
    }

    public FieldDeclVec getFields(boolean allFields) {
	FieldDeclVec fdv = FieldDeclVec.make();
	fdv.append(super.getFields(allFields));
	if (!(peer instanceof escjava.tc.TypeSig)) return fdv;
	escjava.tc.TypeSig ts = (escjava.tc.TypeSig)peer;
	fdv.append(ts.jmlFields);
	if (!allFields) return fdv;
	fdv.append(ts.jmlHiddenFields);
	fdv.append(ts.jmlDupFields);
        return fdv;
    }

} // end of class GhostEnv

/*
 * Local Variables:
 * Mode: Java
 * fill-column: 85
 * End:
 */
