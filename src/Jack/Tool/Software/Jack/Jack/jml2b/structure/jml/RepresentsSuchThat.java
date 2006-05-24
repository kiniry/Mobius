//******************************************************************************
/* Copyright (c) 2002, 2003 GEMPLUS Software Research Labs. All Rights Reserved.
/* Copyright (c) 2003, 2004 INRIA. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: RepresentsSuchThat.java
/*
/*******************************************************************************
/* Warnings/Remarks:
/******************************************************************************/
package jml2b.structure.jml;

import jml2b.IJml2bConfiguration;
import jml2b.exceptions.Jml2bException;
import jml2b.exceptions.PogException;
import jml2b.pog.lemma.FormulaWithPureMethodDecl;
import jml2b.structure.java.Class;
import jml2b.structure.java.JmlFile;
import jml2b.structure.java.Modifiers;
import jml2b.structure.java.ParsedItem;
import jml2b.structure.statement.Expression;
import antlr.collections.AST;

/**
 * This class describes the <i>represents</i> clauses that correspond to a 
 * gluing invariant between a model variable and its dependees represented by a
 * property.
 * @author L. Burdy
 **/
class RepresentsSuchThat extends Represents {

	/**
	 * 
	 */
	private static final long serialVersionUID = 1L;

	/**
	 * Constructs an empty represent clause from a loaded file.
	 * @param jf The Jml file where the clause is defined
	 * @param tree The AST tree representing the clause
	 * @param m The modifiers associated with the clause
	 * @param defining The defining class.
	 **/
	/*@
	  @ requires m != null;
	  @*/
	public RepresentsSuchThat(
		JmlFile jf,
		AST tree,
		Modifiers m,
		Class defining) {
		super(jf, tree, m, defining);
	}

	/**
	 * Constructs a represents clause from another one
	 * @param pi The corresponding parsed item
	 * @param mod The modifiers
	 * @param m The model variable
	 * @param e The glue
	 **/
	private RepresentsSuchThat(
		ParsedItem pi,
		Modifiers mod,
		Modifies m,
		Expression e) {
		super(pi, mod, m, e);
	}

	public Object clone() {
		return new RepresentsSuchThat(
			this,
			(Modifiers) getModifiers(),
			(Modifies) getDepend().clone(),
			(Expression) getGluingInvariant().clone());
	}

    /**
     * @return <code>gluingInvariant</code>
     */
	public FormulaWithPureMethodDecl predToForm(IJml2bConfiguration config) throws PogException {
		try {
			return getGluingInvariant().predToForm(config);
		} catch (Jml2bException je) {
			throw new jml2b.exceptions.InternalError(je.toString());
		}

	}
}