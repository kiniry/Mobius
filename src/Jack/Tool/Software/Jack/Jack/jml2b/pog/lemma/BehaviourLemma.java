//******************************************************************************
/* Copyright (c) 2002, 2003 GEMPLUS Software Research Labs. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: BehaviourLemma.java
/*
/*******************************************************************************
/* Warnings/Remarks:
/******************************************************************************/
package jml2b.pog.lemma;

import java.util.Enumeration;
import java.util.Vector;

import jml2b.exceptions.WrongLabelException;
import jml2b.pog.substitution.Substitution;

/**
 * This class defines lemmas resulting from the proof of a method specification
 * with differents cases.
 * Those lemmas are distinguished between normal and exceptional one.
 * @author L. Burdy
 **/
abstract class BehaviourLemma extends Lemma {

	/**
	 * The set of labelled lemmas.
	 **/
	Vector ensuresLemmas;

	/*@
	  @ invariant ensuresLemmas != null;
	  @ invariant ensuresLemmas.elemType <: \type(LabelledLemma);
	  @*/

	/**
	 * Returns the labelled lemmas enumeration
	 * @return an enumeration of labelled lemmas.
	 **/
	private final Enumeration getEnsuresLemmas() {
		return ensuresLemmas.elements();
	}

	public final boolean proveObvious(Vector hyp, boolean atTheEnd) {
		boolean res = true;
		Enumeration e = getEnsuresLemmas();
		while (e.hasMoreElements()) {
			LabelledLemma l = (LabelledLemma) e.nextElement();
			res = l.proveObvious(hyp, atTheEnd) && res;
		}
		return res;
	}

	public final void garbageIdent() {
		Enumeration e = getEnsuresLemmas();
		while (e.hasMoreElements()) {
			LabelledLemma element = (LabelledLemma) e.nextElement();
			element.garbageIdent();
		}
	}

	public final void oldParam(Vector enume) {
		Enumeration e = getEnsuresLemmas();
		while (e.hasMoreElements()) {
			LabelledLemma l = (LabelledLemma) e.nextElement();
			l.oldParam(enume);
		}
	}

	public final void sub(Substitution s) {
		Enumeration e = getEnsuresLemmas();
		while (e.hasMoreElements()) {
			LabelledLemma l = (LabelledLemma) e.nextElement();
			l.sub(s);
		}
	}

	public final void suppressSpecialOld(int token) {
		Enumeration e = getEnsuresLemmas();
		while (e.hasMoreElements()) {
			LabelledLemma l = (LabelledLemma) e.nextElement();
			l.suppressSpecialOld(token);
		}
	}

	public final void selectLabel(Vector labels) throws WrongLabelException {
		// Constructs a new set of labelled lemmas
		Vector res = new Vector();
		Enumeration e = getEnsuresLemmas();
		while (e.hasMoreElements()) {
			LabelledLemma sg = (LabelledLemma) e.nextElement();
			if (sg.isLabeled(labels)) {
				res.add(sg);
			}
		}
		// If the constructed set is empty, an exception is thrown considering
		// that the implements label statement are not correct.
		if (res.size() == 0)
			throw new WrongLabelException();
		else
			ensuresLemmas = res;
	}

}
