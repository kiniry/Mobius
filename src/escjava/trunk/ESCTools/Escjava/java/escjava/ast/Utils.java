/* Copyright 2000, 2001, Compaq Computer Corporation */

package escjava.ast;


import javafe.ast.ModifierPragma;
import javafe.ast.ModifierPragmaVec;
import javafe.ast.GenericVarDecl;
import escjava.Main;

import javafe.util.*;



public final class Utils {

    /** Finds and returns the first modifier pragma of <code>vdecl</code>
     * that has the tag <code>tag</code>, if any.  If none, returns
     * <code>null</code>.<p>
     *
     * Note, if you want to know whether a variable is <code>non_null</code>,
     * use method <code>NonNullPragma</code> instead, for it properly
     * handles inheritance of <code>non_null</code> pragmas.
     **/

    static public ModifierPragma findModifierPragma(/*@ non_null */ GenericVarDecl vdecl,
                                                    int tag) {
	return findModifierPragma(vdecl.pmodifiers,tag);
    }

    static public ModifierPragma findModifierPragma(ModifierPragmaVec mp,
                                                    int tag) {
        if (mp != null) {
            for (int j = 0; j < mp.size(); j++) {
                ModifierPragma prag= mp.elementAt(j);
                if (prag.getTag() == tag)
                    return prag;
            }
        }
        return null;  // not present
    }

    static public void removeModifierPragma(/*@ non_null */ GenericVarDecl vdecl, int tag) {
	removeModifierPragma(vdecl.pmodifiers,tag);
    }

    static public void removeModifierPragma(ModifierPragmaVec p, int tag) {
        if (p != null) {
            for (int j = 0; j < p.size(); j++) {
                ModifierPragma prag= p.elementAt(j);
                if (prag.getTag() == tag) {
			p.removeElementAt(j);
			--j;
		}
            }
        }
    }

}
