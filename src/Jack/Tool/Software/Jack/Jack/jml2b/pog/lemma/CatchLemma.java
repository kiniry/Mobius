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

import java.util.Set;
import java.util.Vector;

import jml2b.formula.BinaryForm;
import jml2b.formula.Formula;
import jml2b.formula.IFormToken;
import jml2b.formula.TTypeForm;
import jml2b.formula.TerminalForm;
import jml2b.pog.substitution.SubTmpVar;
import jml2b.pog.substitution.Substitution;
import jml2b.structure.java.AClass;
import jml2b.structure.java.Field;
import jml2b.structure.java.Type;

/**
 * This class describes a lemma issued form the proof of a case corresponding
 * to an exceptional behavior in the specification of a method.
 * @author L. Burdy
 **/
class CatchLemma extends ExsuresLabelledLemma {

	/**
	 * The type of the exception.
	 */
	private Type exceptionType;

	/**
	 * The field corresponding to the exception when it is catched.
	 */
	private Field exceptionField;

	/**
	 * The set of exsures lemmas corresponding to the exsures clauses.
	 **/
	private SimpleLemma simpleLemmas;

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
	CatchLemma(
			   Type type,
			   Field f,
		Vector labels,
		SimpleLemma requires,
		SimpleLemma sl,
		SimpleLemma modify,
		SimpleLemma i) {
		super(labels, requires, null, modify, i);
		exceptionField = f;
		exceptionType = type;
		this.simpleLemmas = sl;
	}
	
	public Object clone() {
			return new CatchLemma(
							  exceptionType,
							  exceptionField,
			(Vector) getLabels().clone(),
			(SimpleLemma) getRequires().clone(),
			(SimpleLemma) simpleLemmas.clone(),
			(SimpleLemma) getDoNotModify().clone(),
			(SimpleLemma) getRespectInv().clone());
	}

	public void oldParam(Vector e) {
		super.oldParam(e);
			simpleLemmas.oldParam(e);
	}

	public void sub(Substitution s) {
		super.sub(s);
			simpleLemmas.sub(s);
	}

	public void suppressSpecialOld(int token) {
		super.suppressSpecialOld(token);
		simpleLemmas.suppressSpecialOld(token);
	}

	public void garbageIdent() {
		super.garbageIdent();
			simpleLemmas.garbageIdent();
	}

	public boolean proveObvious(Vector hyp, boolean atTheEnd) {
		boolean res = super.proveObvious(hyp, atTheEnd);
	return simpleLemmas.proveObvious(hyp, atTheEnd) && res;
	}

	/**
	 * Collects all the exceptions type that are declared in the exsures lemma 
	 * of this lemma.
	 * @param s set of {@link jml2b.structure.java.Type}
	 * @see Theorem#getTypesException(Set)
	 **/
	void getTypesException(Set s) {
		s.add(exceptionType);
	}

	void getFields(Set fields) {
		super.getFields(fields);
			simpleLemmas.getFields(fields);
	}

	/**
	 * Returns the lemma to prove to ensure that the thrown of an exception 
	 * ensures the current lemma.
	 * @param vv Instance of the thrown exception.
	 * @param c  Formula containing the class of the thrown exception.
	 * @return the exsures lemmas corresponding to the thrown exceptions
	 **/
	EnsuresLabelledLemma throwException(Formula vv, Formula c, Vector subs) {
		SimpleLemma lv = (SimpleLemma) simpleLemmas.clone();
		SimpleLemma mod = (SimpleLemma) getDoNotModify().clone();
		SimpleLemma inv = (SimpleLemma) getRespectInv().clone();
 		if (exceptionField != null) {
			subs.add(new SubTmpVar(exceptionField.getBName(), vv));
		}

		lv.addGoals((SimpleLemma) getRequires().clone());
//		lv.addGoals((SimpleLemma) l2.clone());
//		lv.addGoals((SimpleLemma) inv.clone());

		BinaryForm t =
			new BinaryForm(
				Jm_IS_SUBTYPE,
				c,
				new TTypeForm(IFormToken.Jm_T_TYPE, exceptionType));

		lv.addImplicToGoal(t, VirtualFormula.LOCALES);
			return new EnsuresLabelledLemma(
			getLabels(),
			new SimpleLemma(),
			lv,
			mod,
			inv);

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
		SimpleLemma mod = (SimpleLemma) getDoNotModify().clone();
		SimpleLemma inv = (SimpleLemma) getRespectInv().clone();
 		if (c.isSubclassOf(exceptionType.getRefType())) {
			tmp= (SimpleLemma) simpleLemmas.clone();
			if (exceptionField != null) {
				subs.add(
					new SubTmpVar(
						exceptionField.getBName(),
						new TerminalForm(vv)));
				mod.sub(
						new SubTmpVar(
										exceptionField.getBName(),
										new TerminalForm(vv)));
				inv.sub(
						new SubTmpVar(
										exceptionField.getBName(),
										new TerminalForm(vv)));
			}
			tmp.addGoals((SimpleLemma) getRequires().clone());
//			lv.addGoals((SimpleLemma) l2.clone());
//			lv.addGoals((SimpleLemma) inv.clone());

			}
		return new EnsuresLabelledLemma(
			getLabels(),
			new SimpleLemma(),
			tmp,
			mod,
			inv);

	}

	/**
	 * Returns whether a exsures lemma catches a given exception.
	 * @param c The class of the tested exception
	 * @return <code>true</code> if the exsures lemma of the current lemma 
	 * contains an exception type that is a super type of the given class, 
	 * <code>false</code> otherwise
	 */
	boolean catches(AClass c) {
		return c.isSubclassOf(exceptionType.getRefType());
	}

}
