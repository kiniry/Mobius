//******************************************************************************
/* Copyright (c) 2002, 2003 GEMPLUS Software Research Labs. All Rights Reserved.
/* Copyright (c) 2004 INRIA. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: Substitution.java
/*
/*******************************************************************************
/* Warnings/Remarks:
/******************************************************************************/
package jml2b.pog.substitution;

import java.io.IOException;

import jml2b.IJml2bConfiguration;
import jml2b.formula.Formula;
import jml2b.formula.IFormToken;
import jml2b.structure.java.IJmlFile;
import jml2b.util.JpoOutputStream;

/**
 * This interface describes a substitution.
 * Let <code>a</code>, <code>b</code>, <code>c</code> be formulas, a 
 * substitution can be the substitution of:
 * <UL>
 * <li> an <i>xxxelements</i> by <code>a</code>
 * <li> <code>arraylength</code> by <code>a</code>
 * <li> a formula by <code>a</code>
 * <li> <code>instances</code> by <code>instances \/ a</code>
 * <li> <code>instances</code> by <code>instances \/ {a}</code>
 * <li> a temporary variable by <code>a</code>
 * <li> <code>typeof</code> by <code>typeof <+ a * {b}</code>
 * <li> <code>typeof</code> by <code>typeof <+ a |-> b</code>
 * <li> a member field by <code>a <+ { b |-> c }</code>
 * </UL>
 * @author L. Burdy
 */
public interface Substitution extends IFormToken {

	/**
	 * Substitution type corresponding to the substitution of an 
	 * <i>xxxelements</i> by <code>a</code>
	 **/
	byte ARRAY_ELEMENT = 0;

	/**
	 * Substitution type corresponding to the substitution of 
	 * <code>arraylength</code> by <code>a</code>
	 **/
	byte ARRAY_LENGTH = 1;

	/**
	 * Substitution type corresponding to the substitution of a formula by 
	 * <code>a</code>
	 **/
	byte FORM = 2;

	/**
	 * Substitution type corresponding to the substitution of 
	 * <code>instances</code> by <code>instances \/ a</code>
	 **/
	byte INSTANCES_SET = 3;

	/**
	 * Substitution type corresponding to the substitution of 
	 * <code>instances</code> by <code>instances \/ {a}</code>
	 **/
	byte INSTANCES_SINGLE = 4;

	/**
	 * Substitution type corresponding to the substitution of a temporary 
	 * variable by <code>a</code>
	 **/
	byte TMP_VAR = 5;

	/**
	 * Substitution type corresponding to the substitution of 
	 * <code>typeof</code> by <code>typeof <+ a * {b}</code>
	 **/
	byte TYPEOF_SET = 6;

	/**
	 * Substitution type corresponding to the substitution of 
	 * <code>typeof</code> by <code>typeof <+ a |-> b</code>
	 **/
	byte TYPEOF_SINGLE = 7;

	/**
	 * Substitution type corresponding to the substitution of a member field by 
	 * <code>a <+ { b |-> c }</code>
	 **/
	byte MEMBER_FIELD = 8;
	
	byte ARRAY_ELEMENT_SINGLE = 9;

	/**
	 * Clones the substitution.
	 * @return the cloned substitution
	 **/
	Object clone();

	/**
	 * Apply the current substitution on a formula.
	 * @param f The formula on which the substitution is applied
	 * @return the substitued formula
	 **/
	/*@
	  @ requires f != null;
	  @*/
	Formula sub(Formula f);

	/**
	 * Apply a substitution on the current substitution.
	 * @param s The substitution to applied
	 **/
	/*@
	  @ requires s != null;
	  @*/
	void sub(Substitution s);

	/**
	 * Saves the substitution in a 
	 * <a href="{@docRoot}/jpov/doc-files/jpo.html"> .jpo file</a>
	 * @param config 
	 * @param s output stream for the jpo file
	 * @param jf 
	 * @throws IOException
	 * @see jml2b.pog.NonObviousGoal#save(DataOutputStream, JmlFile, IJmlFile)
	 **/
	/*@
	  @ requires s != null;
	  @*/
	void save(IJml2bConfiguration config, JpoOutputStream s, IJmlFile jf) throws IOException;

}
