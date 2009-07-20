//******************************************************************************
/* Copyright (c) 2002, 2003 GEMPLUS Software Research Labs. All Rights Reserved.
/* Copyright (c) 2003, 2004 INRIA. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: ExsuresLabelledLemma
/*
/*******************************************************************************
/* Warnings/Remarks:
/*  09/26/2003 : Simplify integration achieved
/******************************************************************************/
package jml2b.pog.lemma;

import java.util.Enumeration;
import java.util.Set;
import java.util.Vector;

import jml2b.exceptions.Jml2bException;
import jml2b.exceptions.PogException;
import jml2b.formula.BinaryForm;
import jml2b.formula.Formula;
import jml2b.formula.IFormToken;
import jml2b.formula.TerminalForm;
import jml2b.pog.substitution.Substitution;
import jml2b.structure.java.AClass;
import jml2b.structure.jml.*;
import jml2b.*;

/**
 * This class describes a lemma issued form the proof of a case corresponding
 * to an exceptional behavior in the specification of a method.
 * @author L. Burdy
 **/
class ExsuresLabelledLemma extends LabelledLemma {

	/**
	 * The set of exsures lemmas corresponding to the exsures clauses.
	 **/
	private Vector exsuresLemmas;

	/*@ 
	  @ private invariant exsuresLemmas != null;
	  @                && exsuresLemmas.elementType <: \type(ExsuresLemma);
	  @*/

	/** 
	 * Constructs a labelled lemma from another one.
	 * @param labels the set of labels
	 * @param requires the lemma corresponding to the <i>requires</i> clause
	 * @param exsuresLemma the lemma corresponding to the <i>exsures</i> clause
	 * @param modify the lemma corresponding to the <i>modifies</i> clause
	 **/
	/*@
	  @ requires exsuresLemmas != null 
	  @       && exsuresLemmas.elementType <: \type(ExsuresLemma);
	  @*/
	ExsuresLabelledLemma(
		Vector labels,
		SimpleLemma requires,
		Vector exsuresLemma,
		SimpleLemma modify,
		SimpleLemma i) {
		super(labels, requires, modify, i);
		this.exsuresLemmas = exsuresLemma;
	}

	/**
	 * Constructs a labelled lemma from a case issued from the specification
	 * of a method.
	 * @param config The current configuration
	 * @param sc The case from which the lemma is initialized
	 * @param l The current invariant
	 * @param fields The set of modifiable fields necessary to calculate the
	 * lemma associated with the <i>modifies</i> clause.
	 * @throws PogException
	 * @see jml2b.pog.LabelledLemma#LabelledLemma(IJml2bConfiguration, SpecCase, Vector)
	 **/
	ExsuresLabelledLemma(
		IJml2bConfiguration config,
		SpecCase sc,
		SimpleLemma l,
		Vector fields)
		throws Jml2bException, PogException {
		super(config, sc, fields, l, new SimpleLemma(), new SimpleLemma());
		exsuresLemmas = new Vector();
		Enumeration e = sc.getExsures();
		while (e.hasMoreElements()) {
			Exsures element = (Exsures) e.nextElement();
			exsuresLemmas.add(
				new ExsuresLemma(
					config,
					element,
					new GoalOrigin(GoalOrigin.EXSURES)));
		}

	}

	public Object clone() {
		Vector tmp = new Vector();
		Enumeration e = exsuresLemmas.elements();
		while (e.hasMoreElements()) {
			ExsuresLemma element = (ExsuresLemma) e.nextElement();
			tmp.add((ExsuresLemma) element.clone());
		}
		return new ExsuresLabelledLemma(
			(Vector) getLabels().clone(),
			(SimpleLemma) getRequires().clone(),
			tmp,
			(SimpleLemma) getDoNotModify().clone(),
			(SimpleLemma) getRespectInv().clone());
	}

	public void oldParam(Vector e) {
		super.oldParam(e);
		Enumeration en = exsuresLemmas.elements();
		while (en.hasMoreElements()) {
			ExsuresLemma element = (ExsuresLemma) en.nextElement();
			element.oldParam(e);
		}
	}

	public void sub(Substitution s) {
		super.sub(s);
		Enumeration e = exsuresLemmas.elements();
		while (e.hasMoreElements()) {
			ExsuresLemma element = (ExsuresLemma) e.nextElement();
			element.sub(s);
		}
	}

	public void suppressSpecialOld(int token) {
		super.suppressSpecialOld(token);
		Enumeration e = exsuresLemmas.elements();
		while (e.hasMoreElements()) {
			ExsuresLemma element = (ExsuresLemma) e.nextElement();
			element.suppressSpecialOld(token);
		}
	}

	public void garbageIdent() {
		super.garbageIdent();
		Enumeration e = exsuresLemmas.elements();
		while (e.hasMoreElements()) {
			ExsuresLemma element = (ExsuresLemma) e.nextElement();
			element.garbageIdent();
		}
	}

	public boolean proveObvious(Vector hyp, boolean atTheEnd) {
		boolean res = super.proveObvious(hyp, atTheEnd);
		Enumeration e = exsuresLemmas.elements();
		while (e.hasMoreElements()) {
			ExsuresLemma element = (ExsuresLemma) e.nextElement();
			res = element.proveObvious(hyp, atTheEnd) && res;
		}
		return res;
	}

	/**
	 * Collects all the exceptions type that are declared in the exsures lemma 
	 * of this lemma.
	 * @param s set of {@link jml2b.structure.java.Type}
	 * @see Theorem#getTypesException(Set)
	 **/
	void getTypesException(Set s) {
		Enumeration e = exsuresLemmas.elements();
		while (e.hasMoreElements()) {
			ExsuresLemma element = (ExsuresLemma) e.nextElement();
			element.getTypesException(s);
		}
	}

	void getFields(Set fields) {
		super.getFields(fields);
		Enumeration e = exsuresLemmas.elements();
		while (e.hasMoreElements()) {
			ExsuresLemma element = (ExsuresLemma) e.nextElement();
			element.getFields(fields);
		}
	}

	/**
	 * Returns the lemma to prove to ensure that the thrown of an exception 
	 * ensures the current lemma.
	 * @param vv Instance of the thrown exception.
	 * @param c  Formula containing the class of the thrown exception.
	 * @return the exsures lemmas corresponding to the thrown exceptions
	 **/
	EnsuresLabelledLemma throwException(Formula vv, Formula c, Vector subs) {
		SimpleLemma tmp = new SimpleLemma();
		Enumeration e = exsuresLemmas.elements();
		while (e.hasMoreElements()) {
			ExsuresLemma el = (ExsuresLemma) e.nextElement();
			if (el.isFalse())
			{
				return new EnsuresLabelledLemma(
				                    			getLabels(),
				                    			new SimpleLemma(),
				                    			new SimpleLemma(new FormulaWithSpecMethodDecl(new TerminalForm(Ja_LITERAL_false, "FALSE")),
				                    			                new GoalOrigin(GoalOrigin.EXSURES)),
				                    			new SimpleLemma(),
				                    			new SimpleLemma());

			}
			tmp.addGoals((SimpleLemma) el.throwException(vv, c, getRequires(), subs));
		}
		return new EnsuresLabelledLemma(
			getLabels(),
			new SimpleLemma(),
			tmp,
			(SimpleLemma) getDoNotModify().clone(),
			(SimpleLemma) getRespectInv().clone());

	}

	/**
	 * Returns the lemma to prove to ensure that the thrown of an exception 
	 * ensures the current lemma.
	 * @param vv Instance of the thrown exception.
	 * @param c  Class of the thrown exception.
	 * @return the exsures lemmas corresponding to the thrown exceptions
	 **/
	EnsuresLabelledLemma throwException(String vv, AClass c, Vector subs) {
		SimpleLemma tmp = new SimpleLemma();
		Enumeration e = exsuresLemmas.elements();
		while (e.hasMoreElements()) {
			ExsuresLemma el = (ExsuresLemma) e.nextElement();
			if (el.isFalse())
			{
				return new EnsuresLabelledLemma(
				                    			getLabels(),
				                    			new SimpleLemma(),
				                    			new SimpleLemma(new FormulaWithSpecMethodDecl(new BinaryForm(
				                    			           					Ja_EQUALS_OP,
				                    			           					new TerminalForm(Ja_LITERAL_false, "FALSE"),
				                    			        					new TerminalForm(IFormToken.Ja_LITERAL_true))),
				                    			                new GoalOrigin(GoalOrigin.EXSURES)),
				                    			new SimpleLemma(),
				                    			new SimpleLemma());

			}
			tmp.addGoals((SimpleLemma) el.throwException(vv, c, getRequires(), subs));
		}
		return new EnsuresLabelledLemma(
			getLabels(),
			new SimpleLemma(),
			tmp,
			(SimpleLemma) getDoNotModify().clone(),
			(SimpleLemma) getRespectInv().clone());

	}

	/**
	 * Returns whether a exsures lemma catches a given exception.
	 * @param c The class of the tested exception
	 * @return <code>true</code> if the exsures lemma of the current lemma 
	 * contains an exception type that is a super type of the given class, 
	 * <code>false</code> otherwise
	 */
	boolean catches(AClass c) {
		Enumeration e = exsuresLemmas.elements();
		while (e.hasMoreElements()) {
			ExsuresLemma element = (ExsuresLemma) e.nextElement();
			if (element.catches(c))
				return true;
		}
		return false;
	}

}
