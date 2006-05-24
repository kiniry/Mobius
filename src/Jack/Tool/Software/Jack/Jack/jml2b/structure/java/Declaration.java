///******************************************************************************
//* Copyright (c) 2002, 2003 GEMPLUS Software Research Labs. All Rights Reserved.
//*------------------------------------------------------------------------------
//* Name: Declaration.java
//*
//********************************************************************************
//* Warnings/Remarks:
//*******************************************************************************/
package jml2b.structure.java;

import jml.JmlDeclParserTokenTypes;
import jml2b.exceptions.Jml2bException;
import jml2b.link.Linkable;
import antlr.collections.AST;

/** 
 * Base class for representing declarations.
 * That is, fields, methods, constructors and invariants.
 *
 * @author A. Requet, L. Burdy 
 **/
public abstract class Declaration
    extends NamedNode
    implements Linkable, JmlDeclParserTokenTypes {

    /** 
     * The modifiers corresponding to the declaration.
     */
    private Modifiers modifiers;
    /**
     * The class that contains the declaration.
     */
    private AClass definingClass;

    /*@
      @ invariant modifiers != null;
      @*/

    public Declaration() {
    	
    }
    
    /**
	 * Creates a new instance with the given modifiers from the given 
	 * parsed item.
	 * 
	 * @param pi the parsed item that is used to initialise the 
	 *     declaration.
	 * @param mods the modifiers that corresponds to the declaration. 
	 */
    /*@
      @ requires mods != null;
      @*/
    public Declaration(ParsedItem pi, Modifiers mods) {
        super(pi);
        modifiers = mods;
    }

	/**
	 * Creates a new declaration from the given AST and modifiers.
	 * 
	 * @param jf the JML file that defines the declaration.
	 * @param tree the AST corresponding to the declaration.
	 * @param mods the modifiers associated to the declaration.
	 * @param defining the class containing the declaration.
	 */
    /*@ 
      @ requires mods != null;
      @*/
    public Declaration(JmlFile jf, AST tree, Modifiers mods, Class defining) {
        super(jf, tree);
        modifiers = mods;
        definingClass = defining;
    }

	/**
	 * Creates a new declaration instance.
	 *  
	 * @param pi the parsed item used to initialise the declaration.
	 * @param mods the modifiers of the declaration.
	 * @param defining the class that contains the declaration.
	 */
    /*@ 
      @ requires mods != null;
      @*/
    public Declaration(ParsedItem pi, Modifiers mods, Class defining) {
        super(pi);
        modifiers = mods;
        definingClass = defining;
    }

	/**
	 * Copy constructor.
	 * 
	 * @param pi the parsed item used to initialise the declaration. 
	 * @param d the declaration whose content should be copied.
	 */
    /*@
      @ requires d != null;
      @*/
    protected Declaration(ParsedItem pi, Declaration d) {
        super(pi);
        modifiers = d.modifiers;
        definingClass = d.definingClass;
    }

	/**
	 * Returns the visibility modifiers associated to this declaration.
	 * @return Modifiers the modifiers.
	 */
    public IModifiers getModifiers() {
        return modifiers;
    }

	/**
	 * Sets the class defining the declaration.
	 * 
	 * @param c the class that defines the declaration.
	 */
    /*@ modifies definingClass; */
    public void setDefiningClass(AClass c) {
        definingClass = c;
    }

	/**
	 * Returns the class that defines the declaration.
	 * 
	 * @return Class the defining class.
	 */
    public AClass getDefiningClass() {
        return definingClass;
    }

	/**
	 * Parses the content of the declaration.
	 * 
	 * @param jmlFile the file the class that defines the declaration is loaded from.
	 * @param ast the AST containing the declaration tree.
	 * @return AST the AST following the declaration.
	 * @throws Jml2bException in case of parse error.
	 */
    public abstract AST parse(JmlFile jmlFile, AST ast) throws Jml2bException;
    // public abstract void link(JmlFile f);

    /** 
     * Returns true if the declaration "<code>this</code>" is visible 
     * from the given class.
     * 
     * @param c the class that is tested for visibility of the declaration.
     * @return <code>true</code> if the visibility modifiers allows the  class
     *     <code>c</code> to see the declaration, <code>false</code> otherwise.
     */
    /*@
      @ requires c != null;
      @*/
    public boolean isVisibleFrom(AClass c) {
        if (c == getDefiningClass()) {
            // if c is the defining class, then the invariant is visible.
            return true;
        }

        if (getModifiers().isExternalVisible()) {
        	// handle case of protected visibility correctly.
			if(getModifiers().isProtectedNotSpecPublic()) {
				// in that case, the modifier is visible from c only if
				// the packages are the same or c inherits from the defining class.
				return c.getPackage() == getDefiningClass().getPackage() ||
					c.isSubclassOf(getDefiningClass());
			}
			
            return true;
        }

        if (getModifiers().isPrivate()) {
            return false;
        }

        // in this case, we know that the modifiers are not private, and
        // are not externally visible => the class has package visibility
        // so it is visible if and only if both classes are defined in the
        // same package
        return c.getPackage() == getDefiningClass().getPackage();
    }
}
