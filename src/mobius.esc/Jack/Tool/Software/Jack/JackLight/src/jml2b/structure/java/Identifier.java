///******************************************************************************
///* Copyright (c) 2002, 2003 GEMPLUS Software Research Labs. All Rights Reserved.
///*------------------------------------------------------------------------------
///* Name: Identifier.java
///*
///*******************************************************************************
///* Warnings/Remarks:
///******************************************************************************/
package jml2b.structure.java;

import java.io.Serializable;
import java.util.Enumeration;

import jml2b.IJml2bConfiguration;
import jml2b.exceptions.Jml2bException;
import jml2b.exceptions.LinkException;
import jml2b.link.LinkContext;
import jml2b.link.LinkInfo;
import jml2b.structure.AField;
import jml2b.structure.AMethod;
import jml2b.util.Profiler;

/** 
 * class representing Java/Jml identifiers. 
 * 
 * @author A. Requet
 **/
public class Identifier extends Profiler implements Serializable {
	private String name;
	// type of the identifier
	public int idType;

	public AClass cl;
	public AMethod mth;
	public Package pkg;
	public AField field;

	public String getName() {
		return name;
	}

	/**
	 * Creates an identifier with given type and content.
	 * 
	 * @param type the type of the identifier.
	 * @param id the content of the identifier.
	 */
	Identifier(int type, String id) {
		name = id;
		idType = type;
	}

	/**
	 * Creates a field identifier.
	 * 
	 * @param f the field this identifier will refer to.
	 */
	public Identifier(AField f) {
		this(ID_FIELD, f.getName());
		field = f;
	}

	/**
	 * Creates a class identifier for the given class.
	 * 
	 * @param c the class this identifier will refer to.
	 */
	public Identifier(AClass c) {
		this(ID_CLASS, c.getName());
		cl = c;
	}

	/**
	 * Creates an identifier for the given method.
	 * 
	 * @param m the method this identifier refers to.
	 */
	public Identifier(AMethod m) {
		this(ID_METHOD, m.getName());
		mth = m;
	}

	/**
	 * Creates an identifier from unknown type with the given string.
	 * 
	 * @param id the content of the identifier.
	 */
	public Identifier(String id) {
		this(ID_UNKNOWN, id);
	}

	public String toString() {
		return name;
	}

	/**
	 * Indicate wether this identifier is equal to the given one.
	 * 
	 * @param i the identifier to compare.
	 * @return boolean <code>true</code> if and only if this identifier 
	 *     is equal to <code>i</code>.
	 */
	public boolean equals(Identifier i) {
		return i != null
			&& name.equals(i.name)
			&& idType == i.idType
			&& cl == i.cl
			&& mth == i.mth
			&& pkg == i.pkg
			&& field == i.field;
	}

	/**
	 * @param ident_box the box that is used for reporting link errors.
	 */
	public LinkInfo linkFieldIdent(
		IJml2bConfiguration config,
		LinkContext ctx,
		ParsedItem ident_box)
		throws Jml2bException {
		String name = getName();

		// search for the name in the local variables and method parameter
		// (p97, The meaning of names)
		AField f = ctx.linkVars.getField(name);
		if (f != null) {
			// we've found the identifier
			idType = Identifier.ID_FIELD;
			field = f;

			return new LinkInfo(f.getType());
		}

		// not found. Search in field of the "current" class
		AClass current_class = ctx.getCurrentClass();
		if (current_class != null) {
			f = current_class.getField(name);
			if (f != null) {
				idType = Identifier.ID_FIELD;
				field = f;
				return new LinkInfo(f.getType());
			}
		}

		// not found. Search in explicitely named imported types
		Package p = ctx.getImportedClassPackage(name);
		if (p != null) {
			// found. The identifier correspond to a class
			idType = Identifier.ID_CLASS;
			cl = p.getAndLoadClass(config, name);
			if (cl == null) {
				// error: the class could not be found
				throw new LinkException(
					"Could not load class " + p.getName() + "." + name,
					ident_box);
			} else {
				return new LinkInfo(new Type(cl));
			}
		}

		// not found. Search in types declared in the current package
		AClass c;
		if (ctx.currentPackage != null) {
			c = ctx.currentPackage.getAndLoadClass(config, name);
			if (c != null) {
				// found. The identifier correspond to a class in the same
				// package
				idType = Identifier.ID_CLASS;
				cl = c;
				return new LinkInfo(new Type(cl));
			}
		}

		// not found. Search in implicitely named imported types
		// java.lang or current_package ?
		Enumeration e = ctx.getImportedPackages();
		while (e.hasMoreElements()) {
			Package tmp = (Package) e.nextElement();
			c = tmp.getAndLoadClass(config, name);
			if (c != null) {
				// found. The identifier correspond to a class in the same
				// package
				idType = Identifier.ID_CLASS;
				cl = c;
				return new LinkInfo(new Type(cl));
			}
		}

		// not found => It is assumed to be a package search in packages

		if (ctx.isFileContext()) {
			// file context => The package is not a subpackage of the current
			// package, but an absolute package
			// => create the package as a children of the root package.
			p = ((JavaLoader) config.getPackage()).getRoot().createAndCheckSubPackage(config, name);
		} else if (ctx.currentPackage != null) {
			p = ctx.currentPackage.createAndCheckSubPackage(config, name);
		} else {
			// throw an exception, since continuing will introduce errors
			// later.
			// Debug.print(Debug.LINKING, "Problem while linking " + name);
			throw new LinkException(
				"Problem while linking " + name + ": current package = null",
				ident_box);
		}

		if (p == null) {
			throw new LinkException(
				"Could not find identifier: " + name,
				ident_box);
		}
		idType = Identifier.ID_PACKAGE;
		pkg = p;
		return new LinkInfo(p);
	}

	// constants representing the types of identifiers

	/**
	 * Identifiers whose type is not known yet.
	 */
	public static final int ID_UNKNOWN = 0;
	/**
	 * Identifiers representing a class
	 */
	public static final int ID_CLASS = 1;

	/**
	 *  Identifiers representing a package:
	 */
	public static final int ID_PACKAGE = 2;

	/// Identifiers representing import (unused)
	///    public static final int ID_IMPORT   = 3;

	/**
	 *  Identifiers corresponding to methods
	 */
	public static final int ID_METHOD = 4;
	/**
	 * Identifiers corresponding to fields.
	 */
	public static final int ID_FIELD = 5;

	static final long serialVersionUID = -4315232328155671622L;
}