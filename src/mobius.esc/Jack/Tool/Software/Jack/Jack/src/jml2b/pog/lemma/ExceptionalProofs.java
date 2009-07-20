//******************************************************************************
/* Copyright (c) 2002, 2003 GEMPLUS Software Research Labs. All Rights Reserved.
/* Copyright (c) 2003, 2004 INRIA. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: ExceptionalProofs
/*
/*******************************************************************************
/* Warnings/Remarks:
/******************************************************************************/
package jml2b.pog.lemma;

import java.util.Enumeration;
import java.util.HashSet;
import java.util.Iterator;
import java.util.Vector;

import jml2b.IJml2bConfiguration;
import jml2b.exceptions.Jml2bException;
import jml2b.exceptions.PogException;
import jml2b.formula.BinaryForm;
import jml2b.formula.Formula;
import jml2b.formula.IFormToken;
import jml2b.formula.TTypeForm;
import jml2b.formula.TerminalForm;
import jml2b.formula.UnaryForm;
import jml2b.pog.substitution.Substitution;
import jml2b.pog.util.ColoredInfo;
import jml2b.pog.util.TemporaryField;
import jml2b.structure.java.AClass;
import jml2b.structure.java.Field;
import jml2b.structure.java.JavaLoader;
import jml2b.structure.java.ParsedItem;
import jml2b.structure.java.Type;
import jml2b.structure.statement.Statement;

/**
 * Class used during the PO generation to treat the proofs corresponding to 
 * exceptional behaviours.
 * @author L. Burdy
 **/
public class ExceptionalProofs extends Proofs {

	/**
	 * 
	 */
	private static final long serialVersionUID = 1L;

	private ExceptionalProofs() {
		super();
	}

	/** 
	 * Constructs a proof from a theorem
	 * @param t The theorem
	 **/
	public ExceptionalProofs(Theorem t) {
		super();
		thl = new TheoremList(t);
	}

	/**
	 * Constructs an exceptional proof from a proof catched by an exception
	 * @param type The catched exception
	 * @param catchParam The catched exception parameter
	 * @param proofs The catched proof
	 **/
	public ExceptionalProofs(Type type, Field catchParam, Proofs proofs) {
		locHyp = proofs.locHyp;
		if (proofs.thl != null)
			thl = proofs.thl.catchException(type, catchParam);
	}

	/**
	 * Clones a proof.
	 * @return the cloned proof 
	 **/
	public Object clone() {
		ExceptionalProofs res = new ExceptionalProofs();
		Enumeration e = locHyp.elements();
		while (e.hasMoreElements()) {
			VirtualFormula vf = (VirtualFormula) e.nextElement();
			res.locHyp.add(vf);
		}
		e = locFlow.elements();
		while (e.hasMoreElements()) {
			ColoredInfo vf = (ColoredInfo) e.nextElement();
			res.locFlow.add(vf);
		}
		res.thl = thl == null ? null : (TheoremList) thl.clone();
		return res;
	}

	/**
	 * Returns the conjonctive formula corresponding to c is not a subtype of 
	 * all the exceptions.
	 * @param c The formula representing a class
	 */
	Formula notSubTypesException(Formula c) {
		if (thl == null)
			return null;
		Formula res = null;
		HashSet hs = new HashSet();
		thl.getTypesException(hs);
		Iterator i = hs.iterator();
		while (i.hasNext()) {
			Type ty = (Type) i.next();
			UnaryForm t =
				new UnaryForm(
					Ja_LNOT,
					new BinaryForm(Jm_IS_SUBTYPE, c, new TTypeForm(IFormToken.Jm_T_TYPE, ty)));
			if (res == null)
				res = t;
			else
				res = Formula.and(res, t);
		}
		return res;
	}

	/**
	 * Returns the conjonctive formula corresponding to c is not a subtype of 
	 * all the exceptions.
	 * @param c The class
	 */
	boolean catches(AClass c) {
		if (thl == null)
			return false;
		else
			return thl.catches(c);
	}

	/**
	 * Calculate the lemmas resulting from the throw of an exception .
	 * @param vv Instance of the thrown exception.
	 * @param c  Formula containing the class of the thrown exception.
	 */
	Proofs throwException(Formula vv, Formula c) {
		Proofs res = new Proofs();
		if (thl != null) {
			Vector subs = new Vector();
			res.thl = thl.throwException(vv, c, subs);
            res.locHyp = locHyp;
            Enumeration e = subs.elements();
            while (e.hasMoreElements()) {
				Substitution  s = (Substitution ) e.nextElement();
				res = res.sub(s);
				
			}
		}
		return res;
	}

	/**
	 * Calculate the lemmas resulting from the throw of an exception .
	 * @param vv Instance of the thrown exception.
	 * @param c  Formula containing the class of the thrown exception.
	 */
	Proofs throwException(String vv, AClass c) {
		Proofs res = new Proofs();
		if (thl != null) {
			Vector subs = new Vector();
			res.thl = thl.throwException(vv, c, subs);
            res.locHyp = locHyp;
            Enumeration e = subs.elements();
            while (e.hasMoreElements()) {
				Substitution  s = (Substitution ) e.nextElement();
				res = res.sub(s);
			}
		}
		return res;
	}

	/**
	 * Calculate the ExceptionalProofs stack resulting from the application of  
	 * the body on the current stack (used to proceed a <i>finally</i>).
     * @param config The current configuration
     * @param body The finally body
     * @param finishOnReturn theorems to ensure if the statement terminates
     * abruptly on a <code>return</code>
     * @param finishOnBreakLab labelled theorems to ensure if the statement
     * terminates abruptly on a <code>break</code>
     * @param finishOnContinueLab labelled theorems to ensure if the statement
     * terminates abruptly on a <code>continue</code>
     * @param exceptionalBehaviour exceptional theorems to ensure if the
     * statement terminates abruply on an exception
	 * @return the new stack
	 * @throws PogException
	 */
	public ExceptionalProofs finallyOnExceptionalBehaviour(
		IJml2bConfiguration config,
		Statement body,
		Proofs finishOnReturn,
		LabeledProofsVector finishOnBreakLab,
		LabeledProofsVector finishOnContinueLab,
		ExceptionalBehaviourStack exceptionalBehaviour)
		throws Jml2bException, PogException {
		String vv = Statement.fresh();
		// s = typeof(vv)
		Formula s =
			Formula.apply(
				TerminalForm.$typeof,
				new TerminalForm(vv));
		Proofs p =
			body.wp(
				config,
				throwException(new TerminalForm(vv), s),
				finishOnReturn,
				finishOnBreakLab,
				finishOnContinueLab, exceptionalBehaviour);
		try {
			Type exc =
				new Type(
					((JavaLoader) config.getPackage()).getJavaLang().getAndLoadClass(config, "Exception"));
			return new ExceptionalProofs(
				exc,
				new TemporaryField(new ParsedItem(), exc, vv),
				p);
		} catch (Jml2bException je) {
			throw new InternalError("Can't find java.lang.Exception.");
		}
	}

}