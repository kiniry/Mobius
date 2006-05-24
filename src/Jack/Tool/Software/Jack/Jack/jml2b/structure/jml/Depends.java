//******************************************************************************
/* Copyright (c) 2002, 2003 GEMPLUS Software Research Labs. All Rights Reserved.
/* Copyright (c) 2004 INRIA. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: Depends
/*
/*******************************************************************************
/* Warnings/Remarks:
/******************************************************************************/
package jml2b.structure.jml;

import java.util.Enumeration;
import java.util.Vector;

import jml2b.IJml2bConfiguration;
import jml2b.exceptions.Jml2bException;
import jml2b.link.LinkContext;
import jml2b.structure.java.Class;
import jml2b.structure.java.Declaration;
import jml2b.structure.java.JmlFile;
import jml2b.structure.java.Modifiers;
import antlr.collections.AST;

/**
 * This class implements a <i>depends</i> clause.
 * @author L. Burdy
 **/
public class Depends extends Declaration {

	/**
	 * 
	 */
	private static final long serialVersionUID = 1L;

	/**
	 * The depends store ref
	 **/
	private Modifies abstractField;

	/**
	 * The set of dependees
	 **/
	private Vector concreteFields;

	/*@
	  @ private invariant concreteFields != null 
	  @               ==> concreteFields.elementType <: \type(Modifies);
	  @*/

	/**
	 * Constructs an empty depends clause that will be fill at parsing.
	 * @param jf The current JML file
	 * @param tree The AST tree
	 * @param m The modifiers of the clause
	 * @param defining The defining class of the clause
	 * @see Depends#parse(JmlFile, AST)
	 **/
	/*@
	  @ requires m != null;
	  @*/
	public Depends(JmlFile jf, AST tree, Modifiers m, Class defining) {
		super(jf, tree, m, defining);
	}

	/**
	 * Parses the dependees
	 * @param jmlFile The current JML file
	 * @param ast The parsed tree
	 **/
	private void parseConcreteFields(JmlFile jmlFile, AST ast)
		throws Jml2bException {
		if (ast.getType() == COMMA) {
			parseConcreteFields(jmlFile, ast.getFirstChild());
			parseConcreteFields(jmlFile, ast.getFirstChild().getNextSibling());
		} else {
			Modifies m = Modifies.create(jmlFile, ast);
			concreteFields.add(m);
		}
	}

	/*@
	  @ requires ast != null;
	  @ requires typeof(ast) <: \type(LineAST);
	  @ modifies invariant;
	  @*/
	public AST parse(JmlFile jmlFile, AST ast) throws Jml2bException {
		//@ set parsed = true;
		abstractField = Modifies.create(jmlFile, ast);
		concreteFields = new Vector();
		parseConcreteFields(jmlFile, ast.getNextSibling());
		return null;
	}

	/*@
	  @ requires parsed;
	  @*/
	public void link(IJml2bConfiguration config, LinkContext f)
		throws Jml2bException {}

	/*@
	  @ requires parsed;
	  @*/
	public int linkStatements(IJml2bConfiguration config, LinkContext f)
		throws Jml2bException {
		abstractField.linkStatements(config, f);
		Enumeration e = concreteFields.elements();
		while (e.hasMoreElements()) {
			Modifies m = (Modifies) e.nextElement();
			m.linkStatements(config, f);
		}
		return 0;
	}

	/**
	 * @return <code>null</code>
	 **/
	public String getName() {
		return null;
	}

	/**
	 * Returns the abstract field.
	 * @return <code>abstractField</code>
	 */
	public Modifies getAbstractField() {
		return abstractField;
	}

	/**
	 * Returns the set of dependees.
	 * @return <code>concreteFields</code>
	 */
	public Vector getConcreteFields() {
		return concreteFields;
	}

}