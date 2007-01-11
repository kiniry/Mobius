//******************************************************************************
/* Copyright (c) 2002, 2003 GEMPLUS Software Research Labs. All Rights Reserved.
/* Copyright (c) 2003, 2004 INRIA. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: Modifiers.java
/*
/********************************************************************************
/* Warnings/Remarks:
/*******************************************************************************/
package jml2b.structure.java;

import java.io.Serializable;

import jml2b.util.Profiler;
import antlr.collections.AST;

/** 
 * Class used to represent Java modifiers
 * .
 * @author A. Requet
 */
public class Modifiers extends  Profiler implements IModifiers, Serializable {
	/**
	 * Integer storing a bitmask of the flags corresponding to the
	 * modifiers.
	 */
	private /*@ spec_public */
	int modifiers;

	/**
	 * Initialise the modifiers from the given AST.
	 * 
	 * @param tree the AST corresponding to the modifiers declaration.
	 */
	//@ requires tree != null;
	//@ modifies modifiers;
	public void parse(AST tree) {
		modifiers = 0;
		String s = tree.getText();
		// look for each of the modifiers and set the flag accordingly

		// Java modifiers
		initFlag(s, "public", ModFlags.PUBLIC);
		initFlag(s, "protected", ModFlags.PROTECTED);
		initFlag(s, "private", ModFlags.PRIVATE);

		initFlag(s, "static", ModFlags.STATIC);
		initFlag(s, "abstract", ModFlags.ABSTRACT);
		initFlag(s, "final", ModFlags.FINAL);

		initFlag(s, "native", ModFlags.NATIVE);
		initFlag(s, "synchronized", ModFlags.SYNCHRONIZED);

		// JML modifiers
		initFlag(s, "non_null", ModFlags.NON_NULL);
		initFlag(s, "pure", ModFlags.PURE);
		initFlag(s, "spec_public", ModFlags.SPEC_PUBLIC);
		initFlag(s, "ghost", ModFlags.GHOST);
		initFlag(s, "model", ModFlags.MODEL);
	}

	/**
	 * Creates a new instance, initialising the modifiers from the 
	 * given AST.
	 *  
	 * @param tree the AST that should be used for initialising the 
	 *     modifiers.
	 */
	//@ requires tree != null;
	public Modifiers(AST tree) {
		parse(tree);
	}

	/**
	 * Creates a new instance, initialising the modifiers from the given
	 * flags.
	 * <code>flags</code> should contain a bitmask of the values defined
	 * in the <code>ModFlags</code> interface.
	 * 
	 * @param flags a bitmask of the modifiers, using the constants defined
	 *     in the <code>ModFlags</code> interface.
	 * @see ModFlags
	 */
	public Modifiers(int flags) {
		modifiers = flags;
	}

	/** 
	 * Returns true if the modifier allow external visibility (that is
	 * visibility outside of the package).
	 * <p>
	 * That is, if the modifier is <code>public</code>, <code>protected</code> or
	 * <code>spec_public</code>.
	 * <p>
	 * It should be noted that if this method returns true, that does <b>not</b> 
	 * means that the corresponding declaration is obligatory visible (it can be
	 * <code>protected</code>).
	 * 
	 * @return boolean <code>true</code> if the modifier allow external 
	 *     visibility, <code>false</code> otherwise.
	 */
	public boolean isExternalVisible() {
		return isSet(ModFlags.PUBLIC)
			|| isSet(ModFlags.PROTECTED)
			|| isSet(ModFlags.SPEC_PUBLIC);
	}

	/**
	 * Indicates wether the modifier has the <code>static</code> modifier set.
	 * 
	 * @return boolean <code>true</code> if the <code>static</code> modifier
	 *     is set, <code>false</code> otherwise.
	 */
	public boolean isStatic() {
		return isSet(ModFlags.STATIC);
	}

	public boolean isFinal() {
		return isSet(ModFlags.FINAL);
	}

	public boolean isJml() {
		return isSet(ModFlags.GHOST) || isSet(ModFlags.MODEL);
	}

	/**
	 * Indicates wether the modifier has the <code>private</code> modifier set.
	 * 
	 * @return boolean <code>true</code> if the <code>private</code> modifier
	 *     is set, <code>false</code> otherwise.
	 */
	public boolean isPrivate() {
		return isSet(ModFlags.PRIVATE);
	}

	/**
	 * Indicates wether the modifier has the <code>protected</code> modifier set.
	 * 
	 * @return boolean <code>true</code> if the <code>protected</code> modifier
	 *     is set, <code>false</code> otherwise.
	 */
	public boolean isProtected() {
		return isSet(ModFlags.PROTECTED);
	}
	
	public boolean isModel() {
		return isSet(ModFlags.MODEL);
	}
	public boolean isNative() {
		return isSet(ModFlags.NATIVE);
	}

	/**
	 * Indicates wether the modifier corresponds to the package visibility.
	 * That is, if neither the <code>public</code>, <code>private</code> nor
	 * <code>protected</code> modifiers are set.
	 * 
	 * @return boolean <code>true</code> if the modifiers corresponds to 
	 *     a <code>package</code> visibility, <code>false</code> otherwise.
	 */
	public boolean isPackageVisible() {
		return !isSet(ModFlags.PUBLIC)
			&& !isSet(ModFlags.PRIVATE)
			&& !isSet(ModFlags.PROTECTED);
	}

	/**
	 * Return <code>true</code> iff the <code>protected</code> modifier is set,
	 * and not the <code>spec_public</code> modifier.
	 * 
	 * @return <code>true</code> iff the <code>protected</code> modifier 
	 * is set, and not the <code>spec_public</code> modifier.
	 */
	public boolean isProtectedNotSpecPublic() {
		return isSet(ModFlags.PROTECTED) && !isSet(ModFlags.SPEC_PUBLIC);
	}

	/** 
	 * Returns <code>true</code> if flag is set, <code>false</code> otherwise.
	 * 
	 * @return <code>true</code> if flag is set, <code>false</code> otherwise.
	 */
	public boolean isSet(int flag) {
		return (modifiers & flag) != 0;
	}

	/** 
	 * Sets the given flag(s).
	 * 
	 * @param flag a bitmask of the flags that should be sets. Valid flags
	 *     are defined in the <code>ModFlags</code> interface.
	 * @see ModFlags
	 */
	//@ modifies modifiers;
	public void setFlag(int flag) {
		modifiers |= flag;
	}

	/** 
	 * Clear the given flag(s).
	 * 
	 * @param flag a bitmask of the flags that should be sets. Valid flags
	 *     are defined in the <code>ModFlags</code> interface.
	 * @see ModFlags
	 */
	//@ modifies modifiers;
	public void clearFlag(int flag) {
		modifiers &= ~flag;
	}

	/**
	 * Sets the given flag in modifiers if ast_string contains 
	 * modifier_string.
	 * 
	 * @param ast_string the string that should be checked for a substring.
	 * @param modifier_string the substring that is searched for
	 * @param flag the flag(s) that should be sets.Valid flags
	 *     are defined in the <code>ModFlags</code> interface.
	 * @see ModFlags
	 */
	//@ requires ast_string != null;
	//@ requires modifier_string != null;
	//@ modifies modifiers;
	private void initFlag(
		String ast_string,
		String modifier_string,
		int flag) {
		if (ast_string.indexOf(modifier_string) != -1) {
			// found substring
			modifiers |= flag;
		}
	}

	/**
	 * Indicates wether the modifier is compatible with the given
	 * modifier.
	 * The modifier is compatible with the given modifiers if both
	 * modifiers are static or non-static, and that the given modifier
	 * is more visible than the current modifier. 
	 * 
	 * @param modifiers the modifiers that should be checked for
	 *     compatibility. 
	 */
	public boolean isCompatible(IModifiers modifiers) {
		if ((modifiers.isStatic() && !isStatic())
			|| (modifiers.isPrivate() && !isPrivate())
			|| (modifiers.isPackageVisible()
				&& !(isPrivate() || isPackageVisible()))
			|| (modifiers.isProtected()
				&& !(isPrivate() || isPackageVisible() || isProtected())))
			return false;
		else
			return true;
	}

	public String emit() {
		String s = "";
		if (isSet(ModFlags.PUBLIC))
			s += "public ";
		if (isSet(ModFlags.PROTECTED))
			s += "protected ";
		if (isSet(ModFlags.PRIVATE))
			s += "private ";

		if (isSet(ModFlags.STATIC))
			s += "static ";
		if (isSet(ModFlags.ABSTRACT))
			s += "abstract ";
		if (isSet(ModFlags.FINAL))
			s += "final ";

		if (isSet(ModFlags.NATIVE))
			s += "native ";
		if (isSet(ModFlags.SYNCHRONIZED))
			s += "synchronized ";

		// JML modifiers
		if (isSet(ModFlags.NON_NULL))
			s += "/*@non_null@*/ ";
		if (isSet(ModFlags.PURE))
			s += "/*@pure@*/ ";
		if (isSet(ModFlags.SPEC_PUBLIC))
			s += "/*@spec_public@*/ ";
		if (isSet(ModFlags.GHOST))
			s += "ghost ";
		if (isSet(ModFlags.MODEL))
			s += "model ";

		return s;
	}

	static final long serialVersionUID = -1546518316935967328L;

	/* (non-Javadoc)
	 * @see jml2b.structure.java.IModifiers#isPure()
	 */
	public boolean isPure() {
		return isSet(ModFlags.PURE);
	}

	public boolean isGhost() {
		// TODO Auto-generated method stub
		return isSet(ModFlags.GHOST);
	}

	public boolean isPublic() {
		
		return isSet(ModFlags.PUBLIC);
	}
}
