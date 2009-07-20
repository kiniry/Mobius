//******************************************************************************
/* Copyright (c) 2002, 2003 GEMPLUS Software Research Labs. All Rights Reserved.
/* Copyright (c) 2003, 2004 INRIA. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: SimpleLemma
/*
/*******************************************************************************
/* Warnings/Remarks:
/*  09/26/2003 : Simplify integration achieved
/******************************************************************************/
package jml2b.pog.lemma;

import java.io.IOException;
import java.io.Serializable;
import java.util.Enumeration;
import java.util.Set;
import java.util.Vector;

import jml2b.IJml2bConfiguration;
import jml2b.exceptions.InternalError;
import jml2b.exceptions.Jml2bException;
import jml2b.exceptions.PogException;
import jml2b.exceptions.WrongLabelException;
import jml2b.formula.BinaryForm;
import jml2b.formula.Formula;
import jml2b.formula.IFormToken;
import jml2b.pog.substitution.Substitution;
import jml2b.pog.util.ColoredInfo;
import jml2b.structure.java.Field;
import jml2b.structure.java.JmlFile;
import jml2b.structure.java.ParsedItem;
import jml2b.structure.java.Type;
import jml2b.structure.jml.JmlExpression;
import jml2b.structure.statement.BinaryExp;
import jml2b.structure.statement.Expression;
import jml2b.util.JpoOutputStream;

/**
 * This class implements a simple lemma, that is a set of goals
 * @author L. Burdy
 **/
public class SimpleLemma extends Lemma implements Serializable {

	/**
	 * Returns the set of {@link ColoredInfo} construct from a set of 
	 * {@link ParsedItem}
	 * @param pis The set of {@link ParsedItem}
	 * @return a vector containing each parsed item converted in a colored info
	 **/
	private static Vector coloredInfos(Vector pis) {
		Vector res = new Vector();
		Enumeration e = pis.elements();
		while (e.hasMoreElements()) {
			ParsedItem element = (ParsedItem) e.nextElement();
			res.add(new ColoredInfo(element));
		}
		return res;
	}

	/**
	 * Returns the set of {@link ColoredInfo} construct from a set of 
	 * {@link ParsedItem}
	 * @param pis The set of {@link ParsedItem}
	 * @return a vector containing each parsed item converted in a colored info
	 **/
	public static Vector coloredInfos(Vector pis, byte comment) {
		Vector res = new Vector();
		Enumeration e = pis.elements();
		while (e.hasMoreElements()) {
			ParsedItem element = (ParsedItem) e.nextElement();
			res.add(new ColoredInfo(element, comment));
		}
		return res;
	}

	/**
	 * The set of {@link Goal}
	 **/
	private Vector goals;
	
	private Vector pureMethodDefs;

	/*@
	  @ private invariant goals != null;
	  @ private invariant goals.elementType <: \type(Goal)
	  @*/

	/**
	 * Constructs a lemma with an empty set of goals
	 **/
	public SimpleLemma() {
		goals = new Vector();
		pureMethodDefs = new Vector();
	}

	/**
	 * Constructs a lemma from an expression. If the expression is conjonctive, 
	 * each part of the conjonction becomes a goal
	 * @param config The current configuration
	 * @param f The expression
	 * @param origin The origin to assign to created goals
	 **/
	public SimpleLemma(
		IJml2bConfiguration config,
		Expression f,
		GoalOrigin origin)
		throws Jml2bException, PogException {
		this(); 
		if (f.isAnd()) {
			goals.addAll(
				new SimpleLemma(
					config,
					((BinaryExp) f).getLeft(),
					origin).goals);
			goals.addAll(
				new SimpleLemma(
					config,
					((BinaryExp) f).getRight(),
					origin).goals);
		} else {
			FormulaWithSpecMethodDecl s = f.predToForm(config);
			if (s.getFormula().getNodeType() == IFormToken.B_BTRUE
				|| (s.getFormula().getNodeType() == IFormToken.Ja_EQUALS_OP
					&& ((BinaryForm) s.getFormula()).getLeft().getNodeType()
						== IFormToken.Ja_LITERAL_true
					&& ((BinaryForm) s.getFormula()).getRight().getNodeType()
						== IFormToken.Ja_LITERAL_true))
				return;
			goals.add(
				new Goal(
				         s.getPureMethodDef(),
					new VirtualFormula(
						VirtualFormula.GOAL,
						s.getFormula(),
						coloredInfos(f.getParsedItems())),
					origin));
		}
	}

	/**
	 * Constructs a lemma from a formula. 
	 * @param f The formula
	 * @param origin The origin to assign to created goals
	 **/
	public SimpleLemma(FormulaWithSpecMethodDecl f, GoalOrigin origin) {
		this();
		goals.add(
			new Goal(
			         f.getPureMethodDef(),
				new VirtualFormula(VirtualFormula.GOAL, f.getFormula(), new ColoredInfo()),
				origin));
	}

	/**
	 * Constructs a lemma from a set of expression. If the expression is 
	 * conjonctive, each part of the conjonction becomes a goal
	 * @param config The current configuration
	 * @param v The set of expression
	 * @param origin The origin to assign to created goals
	 **/
	public SimpleLemma(IJml2bConfiguration config, Vector v, GoalOrigin origin)
		throws Jml2bException, PogException {
		this();
		Enumeration e = v.elements();
		while (e.hasMoreElements()) {
			JmlExpression je = (JmlExpression) e.nextElement();
			FormulaWithSpecMethodDecl f = je.predToForm(config);
			if (f.getFormula().getNodeType() == IFormToken.B_BTRUE
				|| (f.getFormula().getNodeType() == IFormToken.Ja_EQUALS_OP
					&& ((BinaryForm) f.getFormula()).getLeft().getNodeType()
						== IFormToken.Ja_LITERAL_true
					&& ((BinaryForm) f.getFormula()).getRight().getNodeType()
						== IFormToken.Ja_LITERAL_true))
				return;
			goals.add(
				new Goal(
				         f.getPureMethodDef(),
					new VirtualFormula(
						VirtualFormula.GOAL,
						f.getFormula(),
						coloredInfos(je.getParsedItems())),
					origin));
		}
	}

	/**
	 * Constructs a lemma from a loaded one.
	 * @param goals The set of loaded goals
	 **/
	/*@
	  @ requires goals != null && goals.elementType <: \type(Goal);
	  @*/
	public SimpleLemma(Vector goals) {
		this.goals = goals;
	}

	/**
	 * Constructs a simple lemma containing only non obvious goals from a 
	 * lemma. This is performed at the end of the wp calculus to convert all
	 * lemma into simple lemma
	 * @param l The lemma to convert
	 **/
	/*@
	  @ ensures goals.elementType <: \type(NonObviousGoal);
	  @*/
	public SimpleLemma(Lemma l) {
		this();
		FormulaWithSpecMethodDecl tmp;
		if (l instanceof SimpleLemma) {
			SimpleLemma sl = (SimpleLemma) l;
			Enumeration e = sl.getGoals();
			while (e.hasMoreElements()) {
				Goal g = (Goal) e.nextElement();
				goals.add(new NonObviousGoal(g));
				pureMethodDefs.addAll(g.getPureMethodDecl());
			}
		} else if (l instanceof NormalLemma) {
			NormalLemma nl = (NormalLemma) l;
			if (nl.isSimple()) {
				goals = nl.getGoals();
				pureMethodDefs = nl.getPureMethodDefs();
			} else if ((tmp = nl.getFormula()) != null) {
				pureMethodDefs = tmp.getPureMethodDef();
				goals.add(
					new NonObviousGoal(
						new Goal(tmp, new GoalOrigin(GoalOrigin.ENSURES))));
			}
		} else
			throw new InternalError(
				"SimpleLemma.SimpleLemma(LemmaViewer) : wrong type "
					+ l.getClass().toString());
	}

	/**
	 * Clones the simple lemma
	 * @return the cloned simple lemma
	 **/
	public Object clone() {
		SimpleLemma res = new SimpleLemma();
		Enumeration e = goals.elements();
		while (e.hasMoreElements()) {
			Goal g = (Goal) e.nextElement();
			res.goals.add((Goal) g.clone());
		}
		return res;
	}

	/**
	 * Concats two simple lemmas
	 * @param l The simple lemma to concat
	 **/
	public void addGoals(SimpleLemma l) {
		goals.addAll(l.goals);
	}

	/**
	 * Adds a goal to the goal set
	 * @param g The goal to add
	 **/
	public void addGoal(Goal g) {
		goals.add(g);
	}

	/**
	 * Transforms each goal into an implication formula
	 * @param f The implication antecedent
	 * @param origin The origin of <code>f</code>
	 **/
	public void addImplicToGoal(Formula f, byte origin) {
		Enumeration e = goals.elements();
		while (e.hasMoreElements()) {
			Goal g = (Goal) e.nextElement();
			g.addImplicToGoal(f, origin);
		}
	}

	/**
	 * @return the size of the goals set
	 **/
	public int nbPo() {
		return goals.size();
	}

	/*@
	  @ requires goals.elementType <: \type(NonObviousGoal);
	  @*/
	public int nbPoProved(String prover) {
		int res = 0;
		Enumeration e = goals.elements();
		while (e.hasMoreElements()) {
			NonObviousGoal g = (NonObviousGoal) e.nextElement();
			if (g.isProved(prover))
				res++;
		}
		return res;
	}

	/*@
	  @ requires goals.elementType <: \type(NonObviousGoal);
	  @*/
	public int nbPoProved() {
		int res = 0;
		Enumeration e = goals.elements();
		while (e.hasMoreElements()) {
			NonObviousGoal g = (NonObviousGoal) e.nextElement();
			if (g.isProved())
				res++;
		}
		return res;
	}

	public int nbPoChecked() {
		int res = 0;
		Enumeration e = goals.elements();
		while (e.hasMoreElements()) {
			NonObviousGoal g = (NonObviousGoal) e.nextElement();
			if (g.isChecked())
				res++;
		}
		return res;
	}
	public void oldParam(Vector e) {
		Enumeration f = goals.elements();
		while (f.hasMoreElements()) {
			Goal goal = (Goal) f.nextElement();
			goal.oldParam(e);
		}
	}

	public void sub(Substitution s) {
		Enumeration e = goals.elements();
		while (e.hasMoreElements()) {
			Goal goal = (Goal) e.nextElement();
			goal.sub(s);
		}
	}

	public void suppressSpecialOld(int token) {
		Enumeration e = goals.elements();
		while (e.hasMoreElements()) {
			Goal goal = (Goal) e.nextElement();
			goal.suppressSpecialOld(token);
		}
	}

	public void save(IJml2bConfiguration config, JpoOutputStream s, JmlFile jf) throws IOException {
		Enumeration e = goals.elements();
		while (e.hasMoreElements())
			 ((NonObviousGoal) e.nextElement()).save(config, s, jf);
	}

	public boolean proveObvious(Vector hyp, boolean atTheEnd) {
		boolean res = true;
		Vector tmp = new Vector();
		Enumeration e = goals.elements();
		while (e.hasMoreElements()) {
			Goal g = (Goal) e.nextElement();
			if (!g.proveObvious(hyp, atTheEnd)) {
				res = false;
				tmp.add(g);
			}
		}
		goals = tmp;
		return res;
	}

	public void garbageIdent() {
		Enumeration e = goals.elements();
		while (e.hasMoreElements()) {
			Goal element = (Goal) e.nextElement();
			element.garbageIdent();
		}
	}

	public void getFields(Set fields) {
		Enumeration e = goals.elements();
		while (e.hasMoreElements()) {
			Goal element = (Goal) e.nextElement();
			element.getFields(fields);
		}
	}

	/**
	 * Returns an exsures lemma
	 **/
	/*@
	  @ ensures \result <: \type(ExsuresLemma)
	  @*/
	public Lemma catchException(Type type, Field catchParam) {
		return new ExsuresLemma(type, catchParam, this);
	}

	public void selectLabel(Vector labels) throws WrongLabelException {
	}

	/**
	 * Merges the lemma with a loaded set of lemmas.
	 * @param lemmas The loaded set of lemmas
	 **/
	/*@
	  @ requires lemmas.elementType <: \type(SimpleLemma);
	  @*/
	public void mergeWith(jpov.structure.Goal[] goals) {
		for (int i=0; i < goals.length; i++) {
			Enumeration e = getGoals();
			while (e.hasMoreElements()) {
				NonObviousGoal nob = (NonObviousGoal) e.nextElement();
				nob.mergeWith(goals[i]);
			}
		}

	}

	/**
	 * @return the formula corresponding to the conjonction of all the goals
	 **/
	public FormulaWithSpecMethodDecl getFormula() {
		FormulaWithSpecMethodDecl res = null;
		boolean first = true;
		Enumeration e = getGoals();
		while (e.hasMoreElements()) {
			Goal element = (Goal) e.nextElement();
			FormulaWithSpecMethodDecl tmp = element.getFormulaWithPureMethodDecl();
			if (first) {
				first = false;
				res = tmp;
			} else
				res = FormulaWithSpecMethodDecl.and(res, tmp);
		}
		return res;
	}

	/**
	 * Returns the set of goals
	 **/
	public Enumeration getGoals() {
		return goals.elements();
	}

	/**
	 * Returns a goal
	 * @param i The goal index
	 * @return The goal at index <code>i</code>
	 **/
	public Goal getGoal(int i) {
		return (Goal) goals.elementAt(i);
	}

	static final long serialVersionUID = 3261667932288082895L;

	public boolean isFalse() {
		return getFormula().getFormula().isBFalse();
	}

	public Vector getPureMethodDefs() {
		return pureMethodDefs;
	}

}