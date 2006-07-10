//******************************************************************************
/* Copyright (c) 2002, 2003 GEMPLUS Software Research Labs. All Rights Reserved.
/* Copyright (c) 2004 INRIA. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: EnsuresLabelledLemma.java
/*
/*******************************************************************************
/* Warnings/Remarks:
/*  09/26/2003 : Simplify integration achieved
/******************************************************************************/
package jml2b.pog.lemma;

import java.util.Enumeration;
import java.util.Set;
import java.util.Vector;

import jml2b.IJml2bConfiguration;
import jml2b.exceptions.Jml2bException;
import jml2b.exceptions.PogException;
import jml2b.formula.BinaryForm;
import jml2b.formula.ElementsForm;
import jml2b.formula.IFormToken;
import jml2b.formula.IModifiesField;
import jml2b.formula.ModifiedFieldForm;
import jml2b.formula.QuantifiedForm;
import jml2b.formula.QuantifiedVarForm;
import jml2b.formula.TTypeForm;
import jml2b.formula.TerminalForm;
import jml2b.pog.substitution.Substitution;
import jml2b.structure.AField;
import jml2b.structure.java.Class;
import jml2b.structure.java.Field;
import jml2b.structure.java.Identifier;
import jml2b.structure.java.Type;
import jml2b.structure.jml.SpecCase;

/**
 * This class describes a lemma issued form the proof of a case corresponding
 * to a normal behavior in the specification of a method.
 * @author L. Burdy
 */
class EnsuresLabelledLemma extends LabelledLemma {

	/**
	 * The main lemma corresponds to the ensures clause.
	 **/
	private SimpleLemma main;

	/*@
	  @ private invariant main != null;
	  @*/

	/**
	 * Constructs a labelled lemma from a case issued from the specification
	 * of a method. The lemma corresponds to the ensures and the current 
	 * invariant quantified on modified model variables
	 * @param config The current configuration
	 * @param sc the case from which the lemma is initialized
	 * @param l The current invariant
	 * @param fields the set of modifiable fields necessary to calculate the
	 * lemma associated with the <i>modifies</i> clause.
	 * @throws PogException
	 * @see jml2b.pog.LabelledLemma#LabelledLemma(IJml2bConfiguration, SpecCase, Vector)
	 **/
	EnsuresLabelledLemma(
		IJml2bConfiguration config,
		IModifiesField m,
		SpecCase sc,
		SimpleLemma l,
		SimpleLemma sco,
		SimpleLemma ico,
		Vector fields,
		Class definingClass)
		throws Jml2bException, PogException {
		super(config, sc, fields, l, sco, ico);
		main =
			new SimpleLemma(
				config,
				sc.getEnsures(),
				new GoalOrigin(GoalOrigin.ENSURES));
		
		boolean model = false;
		Enumeration e = fields.elements();
		while (e.hasMoreElements()) {
			AField f = (AField) e.nextElement();
			if (f.getModifiers().isModel()) {
				model = true;
				break;
			}
		}
		
		if (model) {
			main.addGoals(l);
			respectInv = (SimpleLemma) sco.clone();
			respectInv.addGoals(ico);
					}

		if (main.nbPo() > 0/*
			&& !(sc.getModifies() instanceof ModifiesNothing)*/) {
			FormulaWithSpecMethodDecl mainF = main.getFormula();

			boolean modelElements = false;

			Vector modelFields = new Vector();
			Vector newModelFields = new Vector();
			e = fields.elements();
			while (e.hasMoreElements()) {
				AField f = (AField) e.nextElement();
				if (f.getModifiers().isModel()) {
					if (f.getType().isArray())
						modelElements = true;
					modelFields.add(f);
					TerminalForm newF = new ModifiedFieldForm(f, m);
					newModelFields.add(newF);
					mainF =
						mainF.sub(
							new TerminalForm(new Identifier(f)),
							newF,
							true);
				}
			}

			if (model) {
				TerminalForm[] newModifiedElements = null;

				if (modelElements) {
					newModifiedElements =
						new TerminalForm[ElementsForm.elements.length];
					for (int i = 0; i < ElementsForm.elements.length; i++) {
						newModifiedElements[i] =
							new ElementsForm(ElementsForm.elements[i]);
						mainF =
							mainF.sub(
								ElementsForm.elements[i],
								newModifiedElements[i],
								true);
					}
				}

				main =
					new SimpleLemma(mainF, new GoalOrigin(GoalOrigin.ENSURES));

				if (modelElements)
					main.addGoals(
						sc.getModifies().modifiesLemmas(
							config,
							modelFields,
							newModelFields,
							newModifiedElements));

				mainF = main.getFormula();

				e = modelFields.elements();
				Enumeration e1 = newModelFields.elements();
				while (e.hasMoreElements()) {
					Field f = (Field) e.nextElement();
					TerminalForm newF = (TerminalForm) e1.nextElement();
					if (f.getModifiers().isStatic()) {
						mainF =
							new FormulaWithSpecMethodDecl(mainF,
							new QuantifiedForm(
								Jm_EXISTS,
								new QuantifiedVarForm(
									newF,
									new TTypeForm(
										IFormToken.T_TYPE,
										f.getType())),
								mainF.getFormula()));
					} else {
						mainF =
							new FormulaWithSpecMethodDecl(mainF,
							new QuantifiedForm(
								Jm_EXISTS,
								new QuantifiedVarForm(
									newF,
									new BinaryForm(
										IS_MEMBER_FIELD,
										new TTypeForm(
											IFormToken.T_TYPE,
											new Type(f.getDefiningClass())),
										new TTypeForm(
											IFormToken.T_TYPE,
											f.getType()))),
								mainF.getFormula()));
					} //else {
					//						mainF =
					//							new QuantifiedForm(
					//								Jm_EXISTS,
					//								new QuantifiedVarForm(
					//									newF,
					//									new BinaryForm(
					//										B_PARTIALFUNCTION,
					//										TerminalForm.REFERENCES,
					//										TerminalForm.REFERENCES)),
					//								mainF);
					//					}
				}

				if (modelElements)
					for (int i = 0; i < ElementsForm.elements.length; i++) {
						mainF =
							new FormulaWithSpecMethodDecl(mainF,
							new QuantifiedForm(
								Jm_EXISTS,
								new QuantifiedVarForm(
									newModifiedElements[i],
									ElementsForm.elements[i].getType()),
								mainF.getFormula()));
					}

				main =
					new SimpleLemma(mainF, new GoalOrigin(GoalOrigin.ENSURES));
			}
		}
	}

	/** 
	 * Constructs a labelled lemma from another one.
	 * @param v the set of labels
	 * @param r the lemma corresponding to the <i>requires</i> clause
	 * @param e the lemma corresponding to the <i>ensures</i> clause
	 * @param m the lemma corresponding to the <i>modifies</i> clause
	 **/
	/*@
	  @ requires e != null;
	  @*/
	EnsuresLabelledLemma(
		Vector v,
		SimpleLemma r,
		SimpleLemma e,
		SimpleLemma m,
		SimpleLemma i) {
		super(v, r, m, i);
		main = e;
	}

	public Object clone() {
		return new EnsuresLabelledLemma(
			(Vector) getLabels().clone(),
			(SimpleLemma) getRequires().clone(),
			(SimpleLemma) main.clone(),
			(SimpleLemma) getDoNotModify().clone(),
			(SimpleLemma) getRespectInv().clone());
	}

	public void oldParam(Vector e) {
		super.oldParam(e);
		main.oldParam(e);
	}

	public void sub(Substitution s) {
		super.sub(s);
		main.sub(s);
	}

	public void suppressSpecialOld(int token) {
		super.suppressSpecialOld(token);
		main.suppressSpecialOld(token);
	}

	public void garbageIdent() {
		super.garbageIdent();
		main.garbageIdent();
	}

	public boolean proveObvious(Vector hyp, boolean atTheEnd) {
		boolean res = super.proveObvious(hyp, atTheEnd);
		return main.proveObvious(hyp, atTheEnd) && res;
	}

	/**
	 * Returns the formula corresponding to this lemma.
	 * @return the conjonction of the formulas issued from the lemmas
	 * corresponding to the <i>requires</i>, <i>ensures</i> and 
	 * <i>modifies</i> clauses.
	 **/
	FormulaWithSpecMethodDecl getFormula() {
		FormulaWithSpecMethodDecl res1 = null;
		Enumeration e = getRequires().getGoals();
		while (e.hasMoreElements()) {
			Goal element = (Goal) e.nextElement();
			FormulaWithSpecMethodDecl tmp = element.getFormulaWithPureMethodDecl();
			res1 = (res1 == null ? tmp : FormulaWithSpecMethodDecl.and(res1, tmp));
		}
		FormulaWithSpecMethodDecl res = null;
		e = main.getGoals();
		while (e.hasMoreElements()) {
			Goal element = (Goal) e.nextElement();
			FormulaWithSpecMethodDecl tmp = element.getFormulaWithPureMethodDecl();
			res = (res == null ? tmp : FormulaWithSpecMethodDecl.and(res, tmp));
		}
		e = getRespectInv().getGoals();
		while (e.hasMoreElements()) {
			Goal element = (Goal) e.nextElement();
			FormulaWithSpecMethodDecl tmp = element.getFormulaWithPureMethodDecl();
			res = (res == null ? tmp : FormulaWithSpecMethodDecl.and(res, tmp));
		}
		e = getDoNotModify().getGoals();
		while (e.hasMoreElements()) {
			Goal element = (Goal) e.nextElement();
			FormulaWithSpecMethodDecl tmp = element.getFormulaWithPureMethodDecl();
			res = (res == null ? tmp : FormulaWithSpecMethodDecl.and(res, tmp));
		}
		if (res1 == null)
			return res;
		else if (res == null)
			return res1;
		else
			return new FormulaWithSpecMethodDecl(res1, res, new BinaryForm(Jm_AND_THEN, res1.getFormula(), res.getFormula()));
	}

	/**
	 * Translates an ensures lemma into an exsures lemma, used when a catch
	 * clause is proceed.
	 * @param type the type of the catched exception
	 * @param catchParam the field of the catch clause
	 * @return an exsures lemma with the same labels and lemmas corresponding
	 * to the <i>requires</i> ans <i>modifies</i> clause and with a lemma
	 * corresponding to a <i>exsures</i> clause construct form the current
	 * main lemma and the parameters
	 */
	CatchLemma catchException(Type type, Field catchParam) {
//		Vector tmp = new Vector();
//		tmp.add(new ExsuresLemma(type, catchParam, main));
		return new CatchLemma(
							  type,
							  catchParam,
			getLabels(),
			getRequires(),
			main,
			getDoNotModify(),
			getRespectInv());
	}

	/**
	 * Returns the set of goals corresponding to this lemma.
	 * @return the set of the goals issued from the lemmas
	 * corresponding to the <i>requires</i>, <i>ensures</i> and 
	 * <i>modifies</i> clauses.
	 **/
	Vector getGoals() {
		Vector res = new Vector();
		Enumeration e = getRequires().getGoals();
		while (e.hasMoreElements()) {
			Goal g = (Goal) e.nextElement();
			res.add(new NonObviousGoal(g));
		}
		e = main.getGoals();
		while (e.hasMoreElements()) {
			Goal g = (Goal) e.nextElement();
			res.add(new NonObviousGoal(g));
		}
		e = getRespectInv().getGoals();
		while (e.hasMoreElements()) {
			Goal g = (Goal) e.nextElement();
			res.add(new NonObviousGoal(g));
		}
		e = getDoNotModify().getGoals();
		while (e.hasMoreElements()) {
			Goal g = (Goal) e.nextElement();
			res.add(new NonObviousGoal(g));
		}
		return res;
	}

	Vector getPureMethodDefs() {
		Vector res = new Vector();
		Enumeration e = getRequires().getGoals();
		while (e.hasMoreElements()) {
			Goal g = (Goal) e.nextElement();
			res.addAll(g.getPureMethodDecl());
		}
		e = main.getGoals();
		while (e.hasMoreElements()) {
			Goal g = (Goal) e.nextElement();
			res.addAll(g.getPureMethodDecl());
		}
		e = getRespectInv().getGoals();
		while (e.hasMoreElements()) {
			Goal g = (Goal) e.nextElement();
			res.addAll(g.getPureMethodDecl());
		}
		e = getDoNotModify().getGoals();
		while (e.hasMoreElements()) {
			Goal g = (Goal) e.nextElement();
			res.addAll(g.getPureMethodDecl());
		}
		return res;
	}
	
	void getFields(Set fields) {
		super.getFields(fields);
		main.getFields(fields);
	}

}
