//******************************************************************************
/* Copyright (c) 2002, 2003 GEMPLUS Software Research Labs. All Rights Reserved.
/* Copyright (c) 2003, 2004 INRIA. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: ExsuresLemma
/*
/*******************************************************************************
/* Warnings/Remarks:
/******************************************************************************/
package jml2b.pog.lemma;

import java.util.Set;
import java.util.Vector;

import jml2b.IJml2bConfiguration;
import jml2b.exceptions.Jml2bException;
import jml2b.exceptions.PogException;
import jml2b.exceptions.WrongLabelException;
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
import jml2b.structure.jml.Exsures;
import jml2b.structure.statement.Expression;
import jml2b.structure.statement.Statement;

/**
 * This class contains the information extracted from an exsures pragma.
 * @author L. Burdy
 **/
public class ExsuresLemma extends Lemma {

	/**
	 * The type of the exception.
	 */
	private Type exceptionType;

	/**
	 * The field corresponding to the exception when it is catched.
	 */
	private Field exceptionField;

	/**
	 * The lemmas associated to the catch of this exception
	 */
	private SimpleLemma lemma;

	/*@
	  @ private invariant exceptionType != null;
	  @ private invariant lemma != null;
	  @*/

	/**
	 * Constructs an exsures lemma
	 * @param t The exception type
	 * @param f The catched variable
	 * @param p The associated lemma
	 **/
	/*@
	  @ requires t != null;
	  @ requires p != null;
	  @*/
	public ExsuresLemma(Type t, Field f, SimpleLemma p) {
		exceptionType = t;
		exceptionField = f;
		lemma = p;
	}

	/**
	 * Constructs an exsures lemma from an exsures clause
	 * @param config The current configuration
	 * @param ex The exsures clause
	 * @param b The expression that should be used to instancie the clause
	 * @param origin The origin of the exsures clause, it can come from a 
	 * method or a loop
	 * @throws PogException
	 **/
	/*@
	  @ requires ex != null;
	  @*/
	public ExsuresLemma(
		IJml2bConfiguration config,
		Exsures ex,
		Expression b,
		GoalOrigin origin)
		throws Jml2bException, PogException {
		exceptionType = ex.getExceptionType();
		exceptionField = ex.getField();
		Expression e = (Expression) ex.getExpression().clone();
		e.old();
		e = (Expression) e.instancie(b);
		lemma = new SimpleLemma(config, e, origin);
	}

	/**
	 * Constructs an exsures lemma from an exsures clause
	 * @param config The current configuration
	 * @param ex The exsures clause
	 * @param origin The origin of the exsures clause, it can come from a 
	 * method or a loop
	 * @throws PogException
	 **/
	/*@
	  @ requires ex != null;
	  @*/
	public ExsuresLemma(
		IJml2bConfiguration config,
		Exsures ex,
		GoalOrigin origin)
		throws Jml2bException, PogException {
		exceptionType = ex.getExceptionType();
		exceptionField = ex.getField();
		Expression e = (Expression) ex.getExpression().clone();
		lemma = new SimpleLemma(config, e, origin);
	}

	public Object clone() {
		return new ExsuresLemma(
			exceptionType,
			exceptionField,
			(SimpleLemma) lemma.clone());
	}

	/**
	 * Returns the name of the catched variable or a temporary variable if there 
	 * is no catched variable
	 * @return a name for the catched variable
	 **/
	public String getBName() {
		if (exceptionField != null)
			return exceptionField.getBName();
		else
			return Statement.freshObject();
	}

	/**
	 * Returns the lemma to prove to ensure that the thrown of an exception 
	 * ensures the current lemma.
	 * @param vv Instance of the thrown exception.
	 * @param c  Formula containing the class of the thrown exception.
	 * @param l1 Requires lemma associated with this lemma
	 * @param l2 Modifies lemma associated with this lemma
	 * @return the exsures lemmas corresponding to the thrown exceptions
	 **/
	Lemma throwException(
		Formula vv,
		Formula c,
		SimpleLemma l1,
		Vector subs) {
		SimpleLemma lv = (SimpleLemma) lemma.clone();
		if (exceptionField != null)
			subs.add(new SubTmpVar(exceptionField.getBName(), vv));

		lv.addGoals((SimpleLemma) l1.clone());
//		lv.addGoals((SimpleLemma) l2.clone());
//		lv.addGoals((SimpleLemma) inv.clone());

		BinaryForm t =
			new BinaryForm(
				Jm_IS_SUBTYPE,
				c,
				new TTypeForm(IFormToken.Jm_T_TYPE, exceptionType));

		lv.addImplicToGoal(t, VirtualFormula.LOCALES);
		return lv;
	}

	/**
	 * Returns the lemma to prove to ensure that the thrown of an exception 
	 * ensures the current lemma.
	 * @param vv Instance of the thrown exception.
	 * @param c  Class of the thrown exception.
	 * @param l1 Requires lemma associated with this lemma
	 * @param l2 Modifies lemma associated with this lemma
	 * @return the exsures lemmas corresponding to the thrown exceptions
	 **/
	Lemma throwException(
		String vv,
		AClass c,
		SimpleLemma l1,
		Vector subs) {
		if (c.isSubclassOf(exceptionType.getRefType())) {
			SimpleLemma lv = (SimpleLemma) lemma.clone();
			if (exceptionField != null)
				subs.add(
					new SubTmpVar(
						exceptionField.getBName(),
						new TerminalForm(vv)));

			lv.addGoals((SimpleLemma) l1.clone());
//			lv.addGoals((SimpleLemma) l2.clone());
//			lv.addGoals((SimpleLemma) inv.clone());

			return lv;
		} else
			return new SimpleLemma();
	}

	/**
	 * @return the lemma where the exception field has been substituted with
	 * <code>vv</code> if <code>c</code> is a subtype of the exception type.
	 **/
	public Lemma throwException(String vv, AClass c, Vector subs) {
		if (c.isSubclassOf(exceptionType.getRefType())) {
			SimpleLemma lv = (SimpleLemma) lemma.clone();
			if (exceptionField != null)
				subs.add(
					new SubTmpVar(
						exceptionField.getBName(),
						new TerminalForm(vv)));

			return lv;
		} else
			return new SimpleLemma();
	}

	/**
	 * @return the lemma under the implication that <code>c</code> is a subtype
	 * of the excpetion type where the exception field has been substituted with
	 * <code>vv</code>.
	 **/
	public Lemma throwException(Formula vv, Formula c, Vector subs) {
		SimpleLemma lv = (SimpleLemma) lemma.clone();
		if (exceptionField != null)
			subs.add(new SubTmpVar(exceptionField.getBName(), vv));

		BinaryForm t =
			new BinaryForm(
				Jm_IS_SUBTYPE,
				c,
				new TTypeForm(IFormToken.Jm_T_TYPE, exceptionType));

		lv.addImplicToGoal(t, VirtualFormula.LOCALES);
		return lv;
	}

	public void oldParam(Vector enume) {
		lemma.oldParam(enume);
	}

	public void suppressSpecialOld(int token) {
		lemma.suppressSpecialOld(token);
	}

	public void garbageIdent() {
		lemma.garbageIdent();
	}

	public void sub(Substitution s) {
		lemma.sub(s);
	}

	public boolean proveObvious(Vector hyp, boolean atTheEnd) {
		return lemma.proveObvious(hyp, atTheEnd);
	}

	public void selectLabel(Vector labels) throws WrongLabelException {
	}

	/**
	 * Adds the exception type to the set
	 **/
	public void getTypesException(Set s) {
		s.add(exceptionType);
	}

	public void getFields(Set fields) {
		lemma.getFields(fields);
	}

	/**
	 * Returns the proof that the exsures lemma implies an exceptionnal
	 * behaviour.
	 * @param ebs The exceptional behaviour
	 * @return the calculated proof
	 **/
	public Proofs impliesExceptional(ExceptionalBehaviourStack ebs) {
		Proofs res = ebs.throwException(getBName(), exceptionType.getRefType());
		res.addHyp(lemma, VirtualFormula.EXSURES);
		return res;
	}

	/**
	 * @return whether <code>c</code> is a subclass of the exception type.
	 **/
	public boolean catches(AClass c) {
		return c.isSubclassOf(exceptionType.getRefType());
	}

	/**
	 * Returns the exceptionType.
	 * @return <code>exceptionType</code>
	 */
	public Type getExceptionType() {
		return exceptionType;
	}

	/**
	 * Returns the lemma.
	 * @return <code>lemma</code>
	 */
	public SimpleLemma getLemma() {
		return lemma;
	}

	/**
	 * Sets the exceptionType.
	 * @param exceptionType The exceptionType to set
	 */
	public void setExceptionType(Type exceptionType) {
		this.exceptionType = exceptionType;
	}

	/**
	 * @return
	 */
	public Field getExceptionField() {
		return exceptionField;
	}

	public boolean isFalse() {
		return lemma.isFalse();
	}

}
