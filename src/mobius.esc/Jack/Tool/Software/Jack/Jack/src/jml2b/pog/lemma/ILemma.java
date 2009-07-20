//******************************************************************************
/* Copyright (c) 2002, 2003 GEMPLUS Software Research Labs. All Rights Reserved.
/* Copyright (c) 2003, 2004 INRIA. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: ILemma
/*
/*******************************************************************************
/* Warnings/Remarks:
/******************************************************************************/
package jml2b.pog.lemma;

import java.util.Vector;

import jml2b.pog.substitution.Substitution;

/**
 * This interface defines the different operations that are performed on lemma 
 * or on goal.
 * @author L. Burdy
 */
public interface ILemma {

	/**
	 * Supress in the lemma the obvious goals.
	 * @return <code>true</code> if the lemma contains only obvious goals,
	 * <code>false</code> otherwise.
	 * @see Proofs#proveObvious(boolean, boolean)
	 **/
	boolean proveObvious(Vector hyp, boolean atTheEnd);

	/**
	 * Adds a <i>old</i> param around the element of the enumeration
	 * corresponding to the parameter of the method.
	 * @param e fields enumeration
	 * @see Theorem#oldParam(Enumeration)
	 **/
	void oldParam(Vector e);

	/**
	 * Apply a substitution to the lemma.
	 * @param s substitution to apply.
	 * @see Proofs#sub(Substitution)
	 **/
	void sub(Substitution s);

	/**
	 * Suppress the <i>Called Old</i> expressions.
	 * @see Theorem#suppressCalledOld()
	 **/
	void suppressSpecialOld(int token);

	/**
	 * Annotates all the fields that appear in the lemma to declare them in 
	 * the Atelier B files.
	 * @see Theorem#garbageIdent()
	 **/
	void garbageIdent();

}
