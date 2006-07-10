//******************************************************************************
/* Copyright (c) 2002, 2003 GEMPLUS Software Research Labs. All Rights Reserved.
/* Copyright (c) 2003 INRIA. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: JmlExpression
/*
/*******************************************************************************
/* Warnings/Remarks:
/******************************************************************************/
package jml2b.structure.jml;

import java.util.Vector;

import jml2b.IJml2bConfiguration;
import jml2b.exceptions.Jml2bException;
import jml2b.exceptions.PogException;
import jml2b.link.TypeCheckable;
import jml2b.pog.lemma.FormulaWithSpecMethodDecl;
import jml2b.structure.statement.Expression;

/**
 * The interface defines methods to apply to a JML expression.
 * @author L. Burdy
 **/
public interface JmlExpression extends TypeCheckable {

	Object clone();

	/**
	 * Instancie the expression.
	 * More <a href="{@docRoot}/jml2b/structure/java/doc-files/instancie.html"> 
	 * informations</a> on instancie.
	 * @return the instanciated expression
	 **/
	JmlExpression instancie();

	/** 
	 * Replaces <code>this</code> with the parameter in the expression.
	 * @param b expression on which the method where the expression occurs is 
	 * called.
	 * @return the modified expression
	 **/
	JmlExpression instancie(Expression b);

	/**
	 * Translates the expression into a formula
     * @param config The current configuration
	 * @return the translated expression
	 * @throws PogException
	 **/
	FormulaWithSpecMethodDecl predToForm(IJml2bConfiguration config)
		throws Jml2bException, PogException;

	/**
	  * Returns the set of parsed items that correspond to this expression
	  * @return the set of parsed item that correspond to the complete 
	  * expression 
	  **/
	Vector getParsedItems();

}