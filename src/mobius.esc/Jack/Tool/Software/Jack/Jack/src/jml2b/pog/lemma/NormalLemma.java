//******************************************************************************
/* Copyright (c) 2002, 2003 GEMPLUS Software Research Labs. All Rights Reserved.
/* Copyright (c) 2003, 2004 INRIA. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: NormalLemma
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
import jml2b.formula.BinaryForm;
import jml2b.structure.java.Field;
import jml2b.structure.java.Method;
import jml2b.structure.java.Type;
import jml2b.structure.jml.SpecCase;

/**
 * This class defines lemmas resulting from the proof of a normal method 
 * specification.
 * <code>ensuresLemmas</code> is a set of {@link EnsuresLabelledLemma}
 * @author L. Burdy
 */
public class NormalLemma extends BehaviourLemma {

	/*@
	  @ invariant ensuresLemmas.elemType <: \type(EnsuresLabelledLemma);
	  @*/

	/**
	 * Creates an empty lemma set.
	 **/
	private NormalLemma() {
		ensuresLemmas = new Vector();
	}

	/**
	 * Creates a set of ensures labelled lemma corresponding to the cases of a 
	 * method specification corresponding to normal behaviours.
	 * @param m The analyzed method
	 * @param l The current invariant
	 * @param fields The set of modifiable fields
	 **/
	public NormalLemma(
		IJml2bConfiguration config,
		Method m,
		SimpleLemma l,
		SimpleLemma sc, 
		SimpleLemma ic,
		Vector fields)
		throws Jml2bException, PogException {
		this();
		Enumeration e = m.getSpecCases(config);
		while (e.hasMoreElements()) {
			SpecCase element = (SpecCase) e.nextElement();
			ensuresLemmas.add(
				new EnsuresLabelledLemma(
					config,
					m,
					element,
					l,
					sc,
					ic,
					fields,
					(jml2b.structure.java.Class) m.getDefiningClass()));
		}
	}

	/**
	 * Creates a normal lemma from another one.
	 * @param v set of lemma
	 **/
	NormalLemma(Vector v) {
		ensuresLemmas = v;
	}

	public Object clone() {
		Vector res = new Vector();
		Enumeration e = ensuresLemmas.elements();
		while (e.hasMoreElements()) {
			EnsuresLabelledLemma el = (EnsuresLabelledLemma) e.nextElement();
			res.add((EnsuresLabelledLemma) el.clone());
		}
		return new NormalLemma(res);
	}

	/**
	 * Creates an exceptional lemma set from the current one and a catched type
	 * with a catched parameter.
	 * @param type The catched type
	 * @param catchParam The catched parameter
	 * @return a {@link ExceptionalLemma} that corresponds to the current lemma
	 * encapsulated in a catched exception.
	 **/
	public Lemma catchException(Type type, Field catchParam) {
		Vector res = new Vector();
		Enumeration e = ensuresLemmas.elements();
		while (e.hasMoreElements()) {
			EnsuresLabelledLemma el = (EnsuresLabelledLemma) e.nextElement();
			res.add(el.catchException(type, catchParam));
		}
		return new ExceptionalLemma(res);

	}

	public void getFields(Set fields) {
		Enumeration e = ensuresLemmas.elements();
		while (e.hasMoreElements()) {
			EnsuresLabelledLemma el = (EnsuresLabelledLemma) e.nextElement();
			el.getFields(fields);
		}
	}

	/**
	 * Gets the formula corresponding to the disjunction of all the goals 
	 * contained in this lemma.
	 * @return the goal to prove to valid this lemma
	 **/
	FormulaWithSpecMethodDecl getFormula() {
		FormulaWithSpecMethodDecl res = null;
		Enumeration e = ensuresLemmas.elements();
		while (e.hasMoreElements()) {
			EnsuresLabelledLemma element =
				(EnsuresLabelledLemma) e.nextElement();
			FormulaWithSpecMethodDecl tmp = element.getFormula();
			if (res == null) {
				res = tmp;
			} else if (tmp != null)
				res = new FormulaWithSpecMethodDecl(res, tmp, new BinaryForm(Jm_OR_ELSE, res.getFormula(), tmp.getFormula()));
		}
		return res;
	}

	/**
	 * Returns whether the lemmas set contains only one lemma
	 * @return <code>true</code> if the size of the set is one, 
	 * <code>false</code> otherwise
	 **/
	/*@ pure */
	boolean isSimple() {
		return ensuresLemmas.size() == 1;
	}

	/**
	 * Returns the goals corresponding the lemma of the lemma set. This method 
	 * is called when the set contains only one element.
	 * @return the set of goals contained in this lemma.
	 **/
	/*@
	  @ requires isSimple()
	  @*/
	Vector getGoals() {
		return ((EnsuresLabelledLemma) ensuresLemmas.elementAt(0)).getGoals();
	}
	
	Vector getPureMethodDefs() {
		return ((EnsuresLabelledLemma) ensuresLemmas.elementAt(0)).getPureMethodDefs();
	}

}
