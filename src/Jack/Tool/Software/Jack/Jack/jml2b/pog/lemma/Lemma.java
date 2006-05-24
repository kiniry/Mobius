//******************************************************************************
/* Copyright (c) 2002, 2003 GEMPLUS Software Research Labs. All Rights Reserved.
/* Copyright (c) 2003, 2004 INRIA. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: LemmaViewer.java
/*
/*******************************************************************************
/* Warnings/Remarks:
/******************************************************************************/
package jml2b.pog.lemma;

import java.io.DataOutputStream;
import java.io.IOException;
import java.util.Set;
import java.util.Vector;

import jml2b.exceptions.WrongLabelException;
import jml2b.formula.Formula;
import jml2b.formula.IFormToken;
import jml2b.structure.java.AClass;
import jml2b.structure.java.Field;
import jml2b.structure.java.JmlFile;
import jml2b.structure.java.Type;
import jml2b.util.Profiler;

/**
 * This class defines a lemma. A lemma is the goal part of a theorem.
 * A lemma can be:
 * <UL>
 * <li> a simple lemma consisting in a list of goal
 * <li> a <i>exsures</i> lemma consisting in an exception and a simple lemma
 * <li> a <i>normal behaviour</i> lemma consisting in a set of labelled simple
 * normal behaviours (requires, modifies, ensures)
 * <li> a <i>exceptional behaviour</i> lemma consisting in a set of labelled
 * simple exceptional behaviours (requires, modifies, exsures).
 * </UL>
 * @author L. Burdy
 */
public abstract class Lemma extends Profiler implements ILemma, IFormToken {

	/**
	 * Returns the number of goals.
	 * @return the number of goals in the lemma
	 * @throws jml2b.exceptions.InternalError when the method is called with a
	 * {@link BehaviourLemma} or a {@link ExsuresLemma}. 
	 * @see Proofs#nbPo()
	 **/
	public int nbPo() {
		throw new jml2b.exceptions.InternalError(
			"LemmaViewer.nbPo() :" + getClass().toString());
	}

	public int nbPoChecked() {
		throw new jml2b.exceptions.InternalError(
			"LemmaViewer.nbPoChecked() :" + getClass().toString());
	}
	/**
	 * Returns the number of goals that are in a specified state.
	 * @param state state of the whished goals number
	 * @return the number of goals in the lemma which have a state 
	 * equals to the paremeter.
	 * @throws jml2b.exceptions.InternalError when the method is called with a
	 * {@link BehaviourLemma} or a {@link ExsuresLemma}. 
	 * @see Proofs#nbProved(int)
	 **/
	public int nbPoProved(String prover) {
		throw new jml2b.exceptions.InternalError(
			"LemmaViewer.nbProved :" + getClass().toString());
	}

	/**
	 * Returns the number of goals that are in a specified state.
	 * @param state state of the whished goals number
	 * @return the number of goals in the lemma which have a state 
	 * equals to the paremeter.
	 * @throws jml2b.exceptions.InternalError when the method is called with a
	 * {@link BehaviourLemma} or a {@link ExsuresLemma}. 
	 * @see Proofs#nbProved(int)
	 **/
	public int nbPoProved() {
		throw new jml2b.exceptions.InternalError(
			"LemmaViewer.nbProved :" + getClass().toString());
	}

	/**
	 * Saves the lemma in a 
	 * <a href="{@docRoot}/jpov/doc-files/jpo.html"> .jpo file</a>
	 * @param s output stream for the jpo file
	 * @param jf current {@link JmlFile}
	 * @throws jml2b.exceptions.InternalError when the method is called with a
	 * {@link BehaviourLemma} or a {@link ExsuresLemma}. 
	 * @throws IOException
	 * @see Theorem#save(DataOutputStream, JmlFile)
	 **/
	void save(DataOutputStream s, JmlFile jf) throws IOException {
		throw new jml2b.exceptions.InternalError(
			"Lemme.save :" + getClass().toString());
	}

	/**
	 * Collects all the exception type that are declared in the exsures lemma of
	 * this lemma.
	 * @param s set of {@link jml2b.structure.java.Type}
	 * @throws jml2b.exceptions.InternalError when the method is called with a
	 * {@link NormalLemma} or a {@link SimpleLemma}. 
	 * @see Theorem#getTypesException(Set)
	 **/
	public void getTypesException(Set s) {
		throw new jml2b.exceptions.InternalError(
			"Lemme.getTypesException :" + getClass().toString());
	}

	public abstract void getFields(Set fields);

	/**
	 * Returns the lemma to prove to ensure that the thrown of an exception 
	 * ensures the current lemma.
	 * @param vv Instance of the thrown exception.
	 * @param c  Formula containing the class of the thrown exception.
	 * @param subs TODO
	 * @return the exsures lemmas corresponfing to the thrown exceptions
	 * @throws jml2b.exceptions.InternalError when the method is called with a
	 * {@link NormalLemma} or a {@link SimpleLemma}. 
	 **/
	public Lemma throwException(Formula vv, Formula c, Vector subs) {
		throw new jml2b.exceptions.InternalError(
			"Lemme.throwException :" + getClass().toString());
	}

	/**
	 * Returns the lemma to prove to ensure that the thrown of an exception 
	 * ensures the current lemma.
	 * @param vv Instance of the thrown exception.
	 * @param c  Class of the thrown exception.
	 * @param subs TODO
	 * @return the exsures lemmas corresponding to the thrown exceptions
	 * @throws jml2b.exceptions.InternalError when the method is called with a
	 * {@link NormalLemma} or a {@link SimpleLemma}. 
	 **/
	public Lemma throwException(String vv, AClass c, Vector subs) {
		throw new jml2b.exceptions.InternalError(
			"Lemme.throwException :" + getClass().toString());
	}

	/**
	 * Returns the lemma corresponding to the current lemma encapsulated in the
	 * fact that it corresponds to a catch of an exception.
	 * @param type catched exception
	 * @param catchParam catched parameter
	 * @return a lemma with exsures clause
	 * @throws jml2b.exceptions.InternalError when the method is called with a
	 * {@link ExsuresLemma} or a {@link ExceptionalLemma}. 
	 */
	public Lemma catchException(Type type, Field catchParam) {
		throw new jml2b.exceptions.InternalError(
			"Lemme.catchException :" + getClass().toString());
	}

	/**
	 * Clones a lemma.
	 * @return the cloned lemma
	 **/
	public abstract Object clone();

	/**
	 * Selects in the labelled lemmas, the cases corresponding to labels.
	 * @param labels set of labels that have to be selected
	 * @throws WrongLabelException if a behaviour lemma does not contain any 
	 * remaining case after the selection.
	 */
	public abstract void selectLabel(Vector labels) throws WrongLabelException;

	/**
	 * Returns whether a exsures lemma catches a given exception.
	 * @param c The class of the tested exception
	 * @return <code>true</code> if the exsures lemma of the current lemma 
	 * contains an exception type that is a super type of the given class, 
	 * <code>false</code> otherwise
	 */
	public boolean catches(AClass c) {
		throw new jml2b.exceptions.InternalError(
			"Lemme.catches :" + getClass().toString());
	}

}
