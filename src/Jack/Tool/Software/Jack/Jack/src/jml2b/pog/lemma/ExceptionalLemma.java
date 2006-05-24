//******************************************************************************
/* Copyright (c) 2002, 2003 GEMPLUS Software Research Labs. All Rights Reserved.
/* Copyright (c) 2003, 2004 INRIA. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: ExceptionalLemma
/*
/*******************************************************************************
/* Warnings/Remarks:
/******************************************************************************/
package jml2b.pog.lemma;

import java.util.Enumeration;
import java.util.Set;
import java.util.Vector;

import jml2b.IJml2bConfiguration;
import jml2b.exceptions.Jml2bException;
import jml2b.exceptions.PogException;
import jml2b.formula.Formula;
import jml2b.structure.java.AClass;
import jml2b.structure.java.Method;
import jml2b.structure.jml.SpecCase;

/**
 * This class defines lemmas resulting from the proof of an exceptional method 
 * specification.
 * <code>ensuresLemmas</code> is a set of {@link ExsuresLabelledLemma}
 * @author L. Burdy
 **/
public class ExceptionalLemma extends BehaviourLemma {

	/*@
	  @ invariant ensuresLemmas.elementType <: \type(ExsuresLabelledLemma)
	  @*/

	/**
	 * Creates an empty lemma set.
	 **/
	private ExceptionalLemma() {
		ensuresLemmas = new Vector();
	}

	/**
	 * Creates a set of exsures labelled lemma corresponding to the cases of a 
	 * method specification corresponding to exceptional behaviours.
	 * @param config The current configuration
	 * @param m The analyzed method
	 * @param fields The set of modifiable fields
	 * @param l The current invariant
	 **/
	public ExceptionalLemma(
		IJml2bConfiguration config,
		Method m,
		Vector fields,
		SimpleLemma l,
		SimpleLemma sco,
		SimpleLemma ico)
		throws Jml2bException, PogException {
		this();
		l.addGoals(sco);
		l.addGoals(ico);
		Enumeration e = m.getSpecCases(config);
		while (e.hasMoreElements()) {
			SpecCase element = (SpecCase) e.nextElement();
			ensuresLemmas.add(
				new ExsuresLabelledLemma(config, element, l, fields));
		}
	}

	/**
	 * Creates an exceptional lemma from another one.
	 * @param v set of lemma
	 **/
	/*@
	  @ requires v != null && v.elementType <: \type(ExsuresLabelledLemma);
	  @*/
	ExceptionalLemma(Vector v) {
		ensuresLemmas = v;
	}

	public Object clone() {
		Vector res = new Vector();
		Enumeration e = ensuresLemmas.elements();
		while (e.hasMoreElements()) {
			ExsuresLabelledLemma el = (ExsuresLabelledLemma) e.nextElement();
			res.add((ExsuresLabelledLemma) el.clone());
		}
		return new ExceptionalLemma(res);
	}

	public void getTypesException(Set s) {
		Enumeration e = ensuresLemmas.elements();
		while (e.hasMoreElements()) {
			ExsuresLabelledLemma el = (ExsuresLabelledLemma) e.nextElement();
			el.getTypesException(s);
		}
	}

	public void getFields(Set fields) {
		Enumeration e = ensuresLemmas.elements();
		while (e.hasMoreElements()) {
			ExsuresLabelledLemma el = (ExsuresLabelledLemma) e.nextElement();
			el.getFields(fields);
		}
	}

	public Lemma throwException(Formula vv, Formula c, Vector subs) {
		Vector tmp = new Vector();
		Enumeration e = ensuresLemmas.elements();
		while (e.hasMoreElements()) {
			ExsuresLabelledLemma el = (ExsuresLabelledLemma) e.nextElement();
			tmp.add(el.throwException(vv, c,subs));
		}
		return new NormalLemma(tmp);

	}

	public Lemma throwException(String vv, AClass c, Vector subs) {
		Vector tmp = new Vector();
		Enumeration e = ensuresLemmas.elements();
		while (e.hasMoreElements()) {
			ExsuresLabelledLemma el = (ExsuresLabelledLemma) e.nextElement();
			tmp.add(el.throwException(vv, c, subs));
		}
		return new NormalLemma(tmp);

	}

	public boolean catches(AClass c) {
		Enumeration e = ensuresLemmas.elements();
		while (e.hasMoreElements()) {
			ExsuresLabelledLemma el = (ExsuresLabelledLemma) e.nextElement();
			if (el.catches(c))
				return true;
		}
		return false;
	}

}
