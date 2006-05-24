//******************************************************************************
/* Copyright (c) 2002, 2003 GEMPLUS Software Research Labs. All Rights Reserved.
/* Copyright (c) 2003, 2004 INRIA. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: LabeledProofsVector.java
/*
/*******************************************************************************
/* Warnings/Remarks:
/*  09/26/2003 : Simplify integration achieved
/******************************************************************************/
package jml2b.pog.lemma;
import java.util.Enumeration;
import java.util.Vector;

import jml2b.IJml2bConfiguration;
import jml2b.exceptions.InternalError;
import jml2b.exceptions.Jml2bException;
import jml2b.exceptions.PogException;
import jml2b.formula.Formula;
import jml2b.structure.statement.Statement;
import jml2b.util.Profiler;

/**
 * This class provides a set of {@link LabeledProofs}.
 * @author L. Burdy
 */
public class LabeledProofsVector extends Profiler {

	/**
	 * List of {@link LabeledProofs}. It can be considered as a stack, since the
	 * order is important due to null label that can appear many times in the
	 * list.
	 **/
	private Vector labeledLemmas;

	/*@
	  @ private invariant labeledLemmas != null;
	  @                && labeledLemmas.elementType <: \type(LabeledProofs);
	  @*/

	/**
	 * Constructs an empty set.
	 **/
	public LabeledProofsVector() {
		labeledLemmas = new Vector();
	}

	/**
	 * Search in the list of labeled proofs, the proof with the corresponding 
	 * label or with a <code>null</code> label if the searched label is 
	 * <code>null</code>. <code>null</code> labels correspond to unlabeled loops.
	 * @param lab the search label
	 * @return the proof corresponding to the searched label
	 * @throws jml2b.exceptions.InternalError when the label is not found.
	 * This corresponds to a bug because the Java compiler ensures that the 
	 * labels used in the <code>break</code> or <code>continue</code> statements 
	 * are defined.
	 **/
	public Proofs searchLabel(Formula lab) {
		Enumeration e = labeledLemmas.elements();

		//@ loop_invariant true;
		//@ loop_exsures (RuntimeException re) false;
		while (e.hasMoreElements()) {
			LabeledProofs l = (LabeledProofs) e.nextElement();
			if ((lab == null && l.getLabel() == null)
				|| (l.getLabel() != null
					&& lab != null
					&& l.getLabel().equals(lab)))
				return (Proofs) l.getLem().clone();
		}
			throw new InternalError(
				"searchLabel : label not found " + lab);
		}

	/**
	 * Add a new labeled proof at the beggining of the list.
	 * @param label label of the new labeled proof
	 * @param l proofs of the new labeled proof
	 **/
	/*@
	  @ requires l != null;
	  @*/
	public void add(Formula label, Proofs l) {
		labeledLemmas.add(0, new LabeledProofs(label, l));
	}

	/**
	 * Removes the last added labeled proof from the list.
	 **/
	public void remove() {
		labeledLemmas.remove(0);
	}

	/**
	 * Applies a WP calculus on all the labeled proofs of the set.
	 * @param body statement on which the WP calculus should be applied
	 * @param finishOnReturn proofs to ensure when the statement finish on a
	 * <code>return</code>
	 * @param finishOnBreakLab set of labeled proofs to ensure when the 
	 * statement finish on a <code>break</code>
	 * @param finishOnContinueLab set of labeled proofs to ensure when the 
	 * statement finish on a <code>continue</code>
	 * @param exceptionalBehaviour exceptional proofs stack to ensures when the
	 * statement finish on an exception thrown
	 * @return a new set of labeled proofs, each labeled proof corresponds to 
	 * the proof resulting of the WP calculus taking the old labeled proof as 
	 * the normal behaviour
	 * @throws PogException (see {@link jml2b.exceptions.PogException for 
	 * more informations})
	 **/
	/*@
	  @ requires body != null;
	  @*/
	public LabeledProofsVector finallyLab(
		IJml2bConfiguration config,
		Statement body,
		Proofs finishOnReturn,
		LabeledProofsVector finishOnBreakLab,
		LabeledProofsVector finishOnContinueLab,
		ExceptionalBehaviourStack exceptionalBehaviour)
		throws Jml2bException, PogException {
		LabeledProofsVector res = new LabeledProofsVector();
		Enumeration e = labeledLemmas.elements();
		//@ loop_invariant true;
		//@ loop_exsures (RuntimeException re) false;
		while (e.hasMoreElements()) {
			LabeledProofs l = (LabeledProofs) e.nextElement();
			res.labeledLemmas.add(
				new LabeledProofs(
					l.getLabel(),
					body.wp(
						config,
						l.getLem(),
						finishOnReturn,
						finishOnBreakLab,
						finishOnContinueLab,
						exceptionalBehaviour)));

		}
		return res;
	}

}