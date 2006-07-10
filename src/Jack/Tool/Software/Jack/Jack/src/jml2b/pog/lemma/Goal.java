//******************************************************************************
/* Copyright (c) 2002, 2003 GEMPLUS Software Research Labs. All Rights Reserved.
/* Copyright (c) 2003, 2004 INRIA. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: Goal
/*
/*******************************************************************************
/* Warnings/Remarks:
/******************************************************************************/
package jml2b.pog.lemma;

import java.util.Enumeration;
import java.util.Set;
import java.util.Vector;

import jml2b.formula.BinaryForm;
import jml2b.formula.Formula;
import jml2b.formula.IFormToken;
import jml2b.pog.substitution.SubArrayElementSingle;
import jml2b.pog.substitution.SubInstances;
import jml2b.pog.substitution.SubMemberField;
import jml2b.pog.substitution.SubStaticOrLocalField;
import jml2b.pog.substitution.SubTypeof;
import jml2b.pog.substitution.Substitution;
import jml2b.pog.util.ColoredInfo;
import jml2b.structure.statement.MyToken;
import jml2b.util.Profiler;

/**
 * This class implements a goal.
 * @author L. Burdy
 */
public class Goal extends Profiler implements MyToken, ILemma, IFormToken {

	/**
	 * Returns whether a formula belongs to a set of formula.
	 * Used during the merging phase.
	 * @param f1 checked formula
	 * @param h2 list of formula
	 * @return <code>true</code> if the formula equals to a formula of the set,
	 * <code>false</code> otherwise
	 * @see Formula#is(Formula)
	 **/
	private static boolean isIn(Formula f1, Vector h2) {
		Enumeration e = h2.elements();
		while (e.hasMoreElements()) {
			Formula f2 = ((VirtualFormula) e.nextElement()).getFormula();
			if (f2.equals(f1))
				return true;
		}
		return false;
	}

	/**
	 * The formula corresponding to the goal.
	 **/
	protected VirtualFormula vf;

	/**
	 * The formula corresponding to the goal when it was created
	 **/
	private Formula originalVf;

	/**
	 * Indication of the fact that the goal has encountered a substitution
	 **/
	private boolean isOriginal = true;

	/**
	 * Set of substitutions applied to the goal.
	 **/
	private Vector subs;
	
	private Vector pureMethodDecl;

	/**
	 * The origin of the goal.
	 **/
	private GoalOrigin origin;

	private transient boolean provedByObviousProver = false;

	/**
	 * Constructs an empty goal that will be fill by the initialize method
	 * @see Goal#initialize(GoalOrigin, VirtualFormula, Formula, Vector)
	 **/
	public Goal() {
	}

	/**
	 * Constructs a goal from a formula and an origin.
	 * @param vf The formula corresponding to this goal.
	 * @param origin The origin of this goal
	 **/
	public Goal(Vector pmd, VirtualFormula vf, GoalOrigin origin) {
		pureMethodDecl = pmd;
		this.vf = vf;
		this.originalVf = vf.getFormula();
		this.origin = origin;
		subs = new Vector();
	}
	
//	/**
//	 * Constructs a goal from a formula and an origin.
//	 * @param vf The formula corresponding to this goal.
//	 * @param origin The origin of this goal
//	 **/
//	public Goal(VirtualFormula vf, GoalOrigin origin) {
//		this.vf = vf;
//		this.originalVf = vf.getFormula();
//		this.origin = origin;
//		subs = new Vector();
//	}

	/**
	 * Constructs a goal from a formula and an origin.
	 * @param f The formula corresponding to this goal.
	 * @param origin The origin of this goal
	 **/
	public Goal(FormulaWithSpecMethodDecl f, GoalOrigin origin) {
		this(
		     f.getPureMethodDef(),
			new VirtualFormula(VirtualFormula.GOAL, f.getFormula(), new ColoredInfo()),
			origin);
	}

	/**
	 * Constructs a goal from another one.
	 * @param origin The origin 
	 * @param vf The formula
	 * @param ovf The original formula
	 * @param subs The set of substitution
	 **/
	Goal(
		GoalOrigin origin,
		Vector pmd,
		VirtualFormula vf,
		Formula ovf,
		Vector subs,
		boolean isOriginal) {
		this.origin = origin;
		pureMethodDecl = pmd;
		this.vf = vf;
		originalVf = ovf;
		this.subs = subs;
		this.isOriginal = isOriginal;
	}

	/**
	 * Initialize a goal from readed informations.
	 * @param origin The origin 
	 * @param vf The formula
	 * @param ovf The original formula
	 * @param subs The set of substitution
	 **/
	void initialize(
		GoalOrigin origin,
		VirtualFormula vf,
		Formula ovf,
		Vector subs) {
		this.origin = origin;
		this.vf = vf;
		originalVf = ovf;
		this.subs = subs;
	}
	/**
	 * Clones the goal
	 * @return the cloned goal
	 **/
	public Object clone() {
		Vector res = new Vector();
		Enumeration e = subs.elements();
		while (e.hasMoreElements()) {
			Substitution s = (Substitution) e.nextElement();
			res.add((Substitution) s.clone());
		}
		return new Goal(origin, pureMethodDecl, vf, originalVf, res, isOriginal);
	}

	/**
	 * Transforms the goal into an implication formula
	 * @param f The implication antecedent
	 * @param origin The origin of <code>f</code>
	 **/
	public final void addImplicToGoal(Formula f, byte origin) {
		vf =
			new VirtualFormula(
				origin,
				new BinaryForm(Jm_IMPLICATION_OP, f, vf.getFormula()),
				vf.getBox());
	}

	public final void oldParam(Vector e) {
		vf =
			new VirtualFormula(
				vf.getOrigin(),
				vf.getFormula().oldParam(e),
				vf.getBox());
	}

	/**
	 * Applies a substitution on the set of substitutions
	 * @param s The subsitution to apply
	 **/
	private final void subInSubs(Substitution s) {
		Enumeration e = subs.elements();
		while (e.hasMoreElements()) {
			Substitution element = (Substitution) e.nextElement();
			element.sub(s);
		}
	}

	public final void sub(Substitution s) {
		VirtualFormula newVf = vf.sub(s);
		if (vf != newVf) {
			isOriginal = false;
			vf = newVf;
			if (s instanceof SubInstances
				|| s instanceof SubTypeof
				|| s instanceof SubMemberField
				|| s instanceof SubArrayElementSingle
				|| s instanceof SubStaticOrLocalField)
				subs.add(s.clone());
			else {
				subInSubs(s);
				originalVf = s.sub(originalVf);
			}
		}
		Vector tmp = new Vector();
		Enumeration e = pureMethodDecl.elements();
		while (e.hasMoreElements()) {
			Formula f = (Formula) e.nextElement();
			tmp.add(s.sub(f));
		}
		pureMethodDecl = tmp;
	}

	public final void suppressSpecialOld(int token) {
		VirtualFormula newVf = vf.suppressSpecialOld(token);
		if (vf != newVf) {
			isOriginal = false;
			vf = newVf;
		}
	}

	public final void garbageIdent() {
		vf.garbageIdent();
		Enumeration e = pureMethodDecl.elements();
		while (e.hasMoreElements()) {
			Formula f = (Formula) e.nextElement();
			f.garbageIdent();
		}
	}

	/**
	  * A goal is obvious if the formula is obvious, if the formula appears in
	  * the hypothesis or if the goal comes from an invariant and it has not 
	  * been modified during the complete generation.
	  * @return <code>true</code> if the goal is obvious, <code>false</code> 
	  * otherwise
	  **/
	public final boolean proveObvious(Vector hyp, boolean atTheEnd) {
		return provedByObviousProver
			|| vf.getFormula().isObvious(atTheEnd)
			|| isIn(vf.getFormula(), hyp)
			|| (atTheEnd
				&& ((origin.getOrigin() == GoalOrigin.MEMBER_INVARIANT
					|| origin.getOrigin() == GoalOrigin.STATIC_INVARIANT)
					&& isOriginal));
	}

	public void getFields(Set fields) {
		vf.getFields(fields);
		Enumeration e = pureMethodDecl.elements();
		while (e.hasMoreElements()) {
			Formula f = (Formula) e.nextElement();
			f.getFields(fields);
		}
	}

	/**
	 * Returns the goal
	 * @return the formula corresponding to the goal
	 **/
	public FormulaWithSpecMethodDecl getFormulaWithPureMethodDecl() {
		return new FormulaWithSpecMethodDecl(pureMethodDecl, vf.getFormula());
	}

	/**
	 * Returns the goal
	 * @return the formula corresponding to the goal
	 **/
	final VirtualFormula getVirtualFormula() {
		return vf;
	}

	/**
	 * Returns the origin of the goal.
	 * @return <code>origin</code>
	 */
	final GoalOrigin getOrigin() {
		return origin;
	}

	/**
	 * Returns the original formula.
	 * @return the original formula corresponding to the goal when it was 
	 * constructed
	 */
	final Formula getOriginalFormula() {
		return originalVf;
	}

	/**
	 * Returns the set of substitutions.
	 * @return <code>subs</code>
	 */
	public final Vector getSubs() {
		return subs;
	}

	/**
	 * Returns the isOriginal.
	 * @return boolean
	 */
	public boolean isOriginal() {
		return isOriginal;
	}

	public void setObvious(boolean b) {
		provedByObviousProver = b;
	}

	public Vector getPureMethodDecl() {
		return pureMethodDecl;
	}

}
