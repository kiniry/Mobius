//******************************************************************************
/* Copyright (c) 2002, 2003 GEMPLUS Software Research Labs. All Rights Reserved.
/* Copyright (c) 2003, 2004 INRIA. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: IdentifierResolver.java
/*
/*******************************************************************************
/* Warnings/Remarks:
/*  09/26/2003 : Simplify integration achieved
/******************************************************************************/
package jml2b.pog.util;

import java.util.Vector;

import jml2b.IJml2bConfiguration;
import jml2b.exceptions.Jml2bException;
import jml2b.structure.AField;
import jml2b.structure.java.AClass;
import jml2b.structure.java.Field;
import jml2b.structure.java.NamedNode;
import jml2b.structure.java.Package;
import jml2b.util.Profiler;

/**
 * This class provides utilities for the treatment of identifiers.
 * Each identifier gets two names, an absolute one and a short one.
 * For example, the absolute name for the field <code>absoluteName</code>
 * of this class would be <code>f_jml2b_util_absoluteName</code> and the short
 * name would be <code>f_absoluteName</code>.
 * Those names are calculated when the <code>processIdent()</code> methods
 * are called.
 * After the PO generation, names are resolved in manner to choose which one
 * will be used in the lemmas. If they are no conflicts the short one will be 
 * used.
 * @see jml2b.pog.IdentifierResolver#bIdents
 * @see jml2b.pog.IdentifierResolver#resolveIdents()
 * @see jml2b.formula.Formula#processIdent()
 * @author L. Burdy
 **/
public class IdentifierResolver extends Profiler {

	/**
	 * The set of identifier.
	 **/
	private static Vector bIdents;

	/*@
	  @ private static invariant bIdents != null 
	  @                   ==> bIdents.elementType <: \type(IdentifierResolver);
	  @*/

	/**
	 * The size of the set of identifier
	 **/
	private static int count = 0;

	/**
	 * Initialize the set of indentifier to the set containing an element
	 * corresponding to the <code>length</code> pseudo field
	 **/
	public static void init(IJml2bConfiguration config) throws Jml2bException {
		// Initialize array of B name with arraylength.
		bIdents = new Vector();
		count = 0;
		bIdents.add(
			count++,
			new IdentifierResolver(
				"f_[_length",
				"arraylength",
				(Field) config.getArray().fields.get(0),
				null,
				false));
	}
	
	/**
	 * Same as above, but softer
	 * @param config
	 * @throws Jml2bException
	 */
	public static void softInit(IJml2bConfiguration config) throws Jml2bException {
		// Initialize array of B name with arraylength.
		bIdents = new Vector();
		count = 0;
	}
	/**
	 * Returns the name in the B syntax of an identifier
	 * @param index The index of the searched identifier
	 **/
	public static String bName(int index) {
		return ((IdentifierResolver) bIdents.get(index)).getBName();
	}

	/**
	 * Adds an identifier in the set of identifier
	 * @param s1 The short name
	 * @param s2 The absolute name
	 * @param n The associated named node
	 * @return The index in the identifier set of the added identifier.
	 **/
	private static int addIdent(String s1, String s2, NamedNode n) {
		int k;
		IdentifierResolver next = null;
		for (k = 0; k < count; k++)
			if (((IdentifierResolver) IdentifierResolver.bIdents.get(k))
				.absoluteNameEquals(s1)) {
				// An identifier with the same absolute name has been found.
				next = (IdentifierResolver) IdentifierResolver.bIdents.get(k);
				while (next != null) {
					if (next.n == n)
						// If it is the same named node, the index is returned
						return k;
					next = next.next;
				}
				// If it another named node, it is added to the list of named node with
				// the same name index.
				next = (IdentifierResolver) IdentifierResolver.bIdents.get(k);
				break;
			}
		if (k == count) {
			IdentifierResolver.bIdents.add(
				new IdentifierResolver(s1, s2, n, next, true));
			count++;
		} else
			IdentifierResolver.bIdents.set(
				k,
				new IdentifierResolver(s1, s2, n, next, true));
		return k;
	}

	/**
	 * Adds a field identifier in the set of identifier.
	 * @param f The field to add
	 * @return The index in the identifier set of the added identifier.
	 **/
	public static int addIdent(AField f) {
		if (f.isLocal())
			return addIdent("l_" + f.getName() + f.getLine(), "l_" + f.getName(), f);
		else
			return addIdent("f_" + getAbsoluteName(f), "f_" + f.getName(), f);
	}

	/**
	 * Adds a class identifier in the set of identifier.
	 * @param c The class to add
	 * @return The index in the identifier set of the added identifier.
	 **/
	public static int addIdent(AClass c) {
		return addIdent("c_" + getAbsoluteName(c), "c_" + c.getName(), c);
	}

	/**
	 * Adds a package identifier in the set of identifier.
	 * @param p The package to add
	 * @return The index in the identifier set of the added identifier.
	 **/
	public static int addIdent(Package p) {
		return addIdent("p_" + getAbsoluteName(p), "p_" + p.name, p);
	}

	/**
	 * Clear the name index of all the named node of the identifier set.
	 * @see jml2b.structure.java.NamedNode#clearName()
	 **/
	public static void clearName() {
		for (int i = 0; i < count; i++)
			 ((IdentifierResolver) bIdents.get(i)).clearNName();
	}

	/**
	 * Resolve identifiers conflict. Allows to set short names to identifier
	 * that are not conflictual
	 **/
	public static void resolveIdents() {
		int i, j;
		on_i : for (i = 0; i < count; i++) {
			for (j = 0; j < count; j++) {
				if (i != j
					&& ((IdentifierResolver) bIdents.get(i)).shortNameEquals(
						((IdentifierResolver) bIdents.get(j))))
					// An identifier with the same short name has been found
					// go to the next one
					continue on_i;
			}
			// No identifier with the same name has been found, so allows to
			// set the short name.
			 ((IdentifierResolver) bIdents.get(i)).setShortName();
		}
	}

	/**
	 * Disallow all identifier of the set of identifier to use their short name
	 **/
	public static void unResolveIdents() {
		int i;
		for (i = 0; i < count; i++) {
			((IdentifierResolver) bIdents.get(i)).unsetShortName();
		}
	}

	/**
	 * Returns the absolute name of a field
	 * @param f The field
	 **/
	public static String getAbsoluteName(AField f) {
		return getAbsoluteName(f.getDefiningClass()) + "_" + f.getName();
	}

	/**
	 * Returns the absolute name of a class
	 * @param c The class
	 **/
	public static String getAbsoluteName(AClass c) {
		String res = "";
		Package p = c.getPackage();
		if (p != null)
			while (p.parent != null) {
				res = p.name + "_" + res;
				p = p.parent;
			}
		res += c.getName();
		return res;
	}

	/**
	 * Returns the absolute name of a package
	 * @param p The package
	 **/
	public static String getAbsoluteName(Package p) {
		String res = "";
		while (p.parent.parent != null) {
			res = p.parent.name + "_" + res;
			p = p.parent;
		}
		return res;
	}

	/**
	 * The absolute name of a field.
	 **/
	private String absoluteName;

	/**
	 * The short name, but potentially ambiguous, name of a field.
	 **/
	private String shortName;

	/**
	 * The <i>named node</i> associated with this field.
	 **/
	NamedNode n;

	/*@
	  @ invariant n != null;
	  @*/

	/**
	 * indicates whether the absolute or the short name should taken into 
	 * account when translating lemmas into B.
	 **/
	boolean getAbsoluteName;

	/**
	 * the next named node with the index
	 **/
	private IdentifierResolver next;

	/**
	 * Constructs an object with the parameters.
	 * @param a absolute name of the field
	 * @param b short name of the field
	 * @param n named node associated to the field
	 **/
	//@ requires n != null;
	private IdentifierResolver(
		String a,
		String b,
		NamedNode n,
		IdentifierResolver next,
		boolean getAbsoluteName) {
		absoluteName = a;
		shortName = b;
		this.n = n;
		this.next = next;
		this.getAbsoluteName = getAbsoluteName;
	}

	/**
	 * Returns the name to be used into the B lemmas.
	 * @return the absolute or the short name depending on 
	 * <code>getAbsoluteName</code>
	 **/
	public String getBName() {
		if (getAbsoluteName)
			return absoluteName;
		else
			return shortName;
	}

	/**
	 * Test whether the absolute name equals the parameter.
	 * @param s tested string
	 * @return <code>true</code> if the string is equal to the absolute name,
	 * <code>false</code> otherwise.
	 **/
	public boolean absoluteNameEquals(String s) {
		return absoluteName.equals(s);
	}

	/**
	 * Test whether the short name equals the parameter.
	 * @param s tested string
	 * @return <code>true</code> if the string is equal to the short name,
	 * <code>false</code> otherwise.
	 **/
	public boolean shortNameEquals(IdentifierResolver ts) {
		return shortName.equals(ts.shortName);
	}

	/**
	 * Indicates that the short name can be used.
	 **/
	public void setShortName() {
		getAbsoluteName = false;
	}

	/**
	 * Indicates that the absolute name can be used.
	 **/
	public void unsetShortName() {
		getAbsoluteName = true;
	}

	/**
	 * Clear the name index.
	 * @see jml2b.structure.java.NamedNode#clearName()
	 **/
	public void clearNName() {
		n.clearName();
		if (next != null)
			next.clearNName();
	}

}
