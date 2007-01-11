//******************************************************************************
/* Copyright (c) 2002, 2003 GEMPLUS Software Research Labs. All Rights Reserved.
/* Copyright (c) 2004 INRIA. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: Constructor.java
/*
/********************************************************************************
/* Warnings/Remarks:
/*******************************************************************************/
package jml2b.structure.java;

import java.util.Enumeration;
import java.util.Vector;

import jml.LineAST;
import jml2b.IJml2bConfiguration;
import jml2b.exceptions.Jml2bException;
import jml2b.exceptions.PogException;
import jml2b.structure.AField;
import jml2b.structure.jml.ModifiesList;
import jml2b.structure.jml.SpecCase;
import antlr.collections.AST;

/**
 * Specialisation of the <code>Method</code> class suitable for
 * representing constructors.
 * 
 * Constructors are handled the same as methods, excepted that they
 * are parsed a bit differently, due to the fact that they do not
 * declare a return type.
 * 
 * @author A. Requet
 */
public class Constructor extends Method {

	Vector saved;

	//@ requires defining != null;
	Constructor(JmlFile jf, AST tree, IModifiers mods, Class defining)
		throws Jml2bException {
		super(jf, tree, mods, defining);
		// set the name to the name of the class, since this could break 
		// statement.
		name = defining.getName();
	}

	//@ requires defining != null;
	Constructor(ParsedItem pi, IModifiers mods, Class defining)
		throws Jml2bException {
		super(pi, mods, defining);
		// set the name to the name of the class, since this could break 
		// statement.
		name = defining.getName();
	}

	/*@ requires ast != null;
	  @ requires \typeof(ast) <: \type(LineAST);
	  @ modifies firstLine, returnType;
	  @*/
	public AST parse(JmlFile jmlFile, AST ast) throws Jml2bException {
		firstLine = ((LineAST) ast).line;
		setReturnType(null);
		return parseAfterRetType(jmlFile, ast);
	}

	public boolean isConstructor() {
		return true;
	}

	public void completeModifiesWithOwnFields(IJml2bConfiguration config)
		throws PogException, Jml2bException {
		// Save the current specification to restore it after proof
		// generation.
		saved = new Vector();
		Enumeration e = getSpecCases(config);
		while (e.hasMoreElements()) {
			SpecCase element = (SpecCase) e.nextElement();
			saved.add(element.clone());
		}
		
		Vector ownNonStaticFields = new Vector();
		e = ((Class) getDefiningClass()).getOwnFields().elements();
		while (e.hasMoreElements()) {
			AField f = (AField) e.nextElement();
			if (!f.getModifiers().isStatic())
				ownNonStaticFields.add(f);
		}

		if (ownNonStaticFields.size() > 0) {
			e = getSpecCases(config);
			while (e.hasMoreElements()) {
				SpecCase element = (SpecCase) e.nextElement();
				ModifiesList ml =
					new ModifiesList(ownNonStaticFields.elements());
				ml.instancie(config);
				ml.processIdent();
				element.completeModifiesWithOwnFields(ml);
			}
		}
	}

	public void restore() {
		specCases = saved;
	}

	static final long serialVersionUID = -8652681423258987194L;
}
