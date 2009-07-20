//******************************************************************************
/* Copyright (c) 2002, 2003 GEMPLUS Software Research Labs. All Rights Reserved.
/* Copyright (c) 2003, 2004 INRIA. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: LabelledLemma.java
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
import jml2b.formula.IFormToken;
import jml2b.pog.substitution.Substitution;
import jml2b.structure.jml.SpecCase;
import jml2b.structure.statement.Expression;

/**
 * This class describes an abstract labelled lemma, that is a lemma issued
 * from the proof of a labelled case in the specification of a method. This
 * lemma contains labels, lemmas associated to the prove of the requires
 * clause and lemmas associated to the prove of the modifies clause.
 * @author L. Burdy
 */
abstract class LabelledLemma
	extends jml2b.util.Profiler
	implements ILemma, IFormToken {

	/**
	 * The set of labels.
	 **/
	private Vector labels;

	/**
	 * The lemma associated to the proof of the <i>requires</i> clause.
	 **/
	private SimpleLemma requires;

	/**
	 * The lemma associated to the proof of the <i>modifies</i> clause.
	 **/
	private SimpleLemma doNotModify;

	/**
	 * The inv lemma corresponds to the invariant.
	 **/
	protected SimpleLemma respectInv;

	/*@
	  @ private invariant labels != null;
	  @                && labels.elementType <: \type(Expression);
	  @*/

	/**
	 * Constructs a labelled lemma from a case issued from the specification
	 * of a method.
	 * @param config The current configuration
	 * @param sc The case from which the lemma is initialized
	 * @param fields The set of modifiable fields necessary to calculate the
	 * lemma associated with the <i>modifies</i> clause.
	 * @throws PogException
	 **/
	protected LabelledLemma(
		IJml2bConfiguration config,
		SpecCase sc,
		Vector fields,
		SimpleLemma inv,
		SimpleLemma sco,
		SimpleLemma ico)
		throws Jml2bException, PogException {
		labels = sc.getLabels();
		requires =
			new SimpleLemma(
				config,
				sc.getRequires(),
				new GoalOrigin(GoalOrigin.ENSURES));
		doNotModify = sc.modifiesLemmas(config, fields);
		respectInv = (SimpleLemma) inv.clone();
		respectInv.addGoals(sco);
		respectInv.addGoals(ico);
	}

	/** Constructs a labelled lemma from another one.
	 * @param v the set of labels
	 * @param r the lemma corresponding to the <i>requires</i> clause
	 * @param m the lemma corresponding to the <i>modifies</i> clause
	 **/
	protected LabelledLemma(Vector v, SimpleLemma r, SimpleLemma m, SimpleLemma i) {
		labels = v;
		requires = r;
		doNotModify = m;
		respectInv = i;
	}

	/**
	 * Clones the labelled lemma.
	 * @return the cloned lemma
	 **/
	public abstract Object clone();

	public boolean proveObvious(Vector hyp, boolean atTheEnd) {
		boolean res = requires.proveObvious(hyp, atTheEnd);
		res = doNotModify.proveObvious(hyp, atTheEnd) && res;
		return respectInv.proveObvious(hyp, atTheEnd) && res;
	}

	public void oldParam(Vector e) {
		requires.oldParam(e);
		doNotModify.oldParam(e);
	}

	public void sub(Substitution s) {
		requires.sub(s);
		doNotModify.sub(s);
		respectInv.sub(s);
	}

	public void suppressSpecialOld(int token) {
	}

	public void garbageIdent() {
		requires.garbageIdent();
		doNotModify.garbageIdent();
		respectInv.garbageIdent();
	}

	/**
	 * Check whether some labels belong to the labels of this lemma.
	 * @param labels the set of tested labels
	 * @return <code>true</code> if a label of the set of tested labels
	 * belongs to the labels of the current lemma, <code>false</code> 
	 * otherwise
	 */
	final boolean isLabeled(Vector labels) {
		Enumeration e = labels.elements();
		while (e.hasMoreElements()) {
			Expression ex = (Expression) e.nextElement();
			Enumeration e1 = this.labels.elements();
			while (e1.hasMoreElements()) {
				Expression ex1 = (Expression) e1.nextElement();
				if (ex1.equals(ex))
					return true;
			}
		}
		return false;
	}

	void getFields(Set fields) {
		doNotModify.getFields(fields);
		requires.getFields(fields);
	}

	/**
	 * Returns doNotModify.
	 * @return the lemma associated with the <i>modifies</i> clause
	 */
	protected final SimpleLemma getDoNotModify() {
		return doNotModify;
	}

	/**
	 * @return
	 */
	public SimpleLemma getRespectInv() {
		return respectInv;
	}

	/**
	 * Returns the set of labels.
	 * @return <code>labels</code>
	 */
	protected final Vector getLabels() {
		return labels;
	}

	/**
	 * Returns the lemma associated with the <i>requires</i> clause.
	 * @return <code>requires</code>
	 */
	protected final SimpleLemma getRequires() {
		return requires;
	}

}
