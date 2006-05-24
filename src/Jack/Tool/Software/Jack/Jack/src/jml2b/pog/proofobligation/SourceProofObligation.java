//******************************************************************************
/* Copyright (c) 2002, 2003 GEMPLUS Software Research Labs. All Rights Reserved.
/* Copyright (c) 2003, 2004 INRIA. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: SourceProofObligation
/*
/*******************************************************************************
/* Warnings/Remarks:
/******************************************************************************/
package jml2b.pog.proofobligation;

import jml.JmlDeclParserTokenTypes;
import jml2b.formula.IFormToken;
import jml2b.pog.lemma.Theorem;
import jml2b.pog.util.ColoredInfo;
import jml2b.structure.java.Class;
import jml2b.structure.statement.Statement;

/**
 * This abstract class describes a proof obligation and facilities to calculate 
 * them at source level.
 * 
 * @author L. Burdy
 */
public abstract class SourceProofObligation
	extends ProofObligation
	implements JmlDeclParserTokenTypes, IFormToken {

	/**
	 * Method counter usefull to give a uniq name to each method.
	 **/
	public static int methodCount;

	/**
	 * Name of the lemmas constructed from this proof obligation
	 **/
	private String name;

	/**
	 * Class from which this proof obligation is issued
	 **/
	private Class cl;

	/**
	 * The colored information corresponding to the method
	 **/
	private ColoredInfo box;

	/**
	 * The statement that should ensures the proof obligation
	 **/
	private Statement body;

	/**
	 * The theorem to ensure as normal behaviour
	 **/
	private Theorem phi1;

	/**
	 * The theorem to ensure as exceptional behaviour
	 **/
	private Theorem phi7;

	/*@
	  @ private invariant body != null;
	  @                && cl != null;
	  @*/

	/**
	 * Constructs a proof obligation
	 * @param name The name of the PO
	 * @param b The body
	 * @param p1 The normal behaviour proof
	 * @param p7 The exceptional behaviour proof
	 * @param c The current class
	 * @param ci The colored info
	 **/
	/*@
	  @ requires b != null;
	  @ requires c != null;
	  @*/
	SourceProofObligation(
		String name,
		Statement b,
		Theorem p1,
		Theorem p7,
		Class c,
		ColoredInfo ci) {
		this.name = name;
		body = b;
		phi1 = p1;
		phi7 = p7;
		cl = c;
		box = ci;
	}

	/**
	 * Returns the box.
	 * @return ColoredInfo
	 */
	ColoredInfo getBox() {
		return box;
	}

	/**
	 * Returns the cl.
	 * @return Class
	 */
	Class getCl() {
		return cl;
	}

	/**
	 * Returns the name.
	 * @return String
	 */
	String getName() {
		return name;
	}

	/**
	 * Returns the phi1.
	 * @return Theorem
	 */
	Theorem getPhi1() {
		return phi1;
	}

	/**
	 * Returns the phi7.
	 * @return Theorem
	 */
	Theorem getPhi7() {
		return phi7;
	}

	/**
	 * Returns the body.
	 * @return Statement
	 */
	Statement getBody() {
		return body;
	}

}