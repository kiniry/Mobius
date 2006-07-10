//******************************************************************************
/* Copyright (c) 2002, 2003 GEMPLUS Software Research Labs. All Rights Reserved.
/* Copyright (c) 2003, 2004 INRIA. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: ModifiesNothing
/*
/*******************************************************************************
/* Warnings/Remarks:
/*  09/26/2003 : Simplify integration achieved
/******************************************************************************/
package jml2b.structure.jml;

import java.util.Enumeration;
import java.util.Vector;

import jml2b.IJml2bConfiguration;
import jml2b.exceptions.Jml2bException;
import jml2b.exceptions.PogException;
import jml2b.formula.BinaryForm;
import jml2b.formula.ElementsForm;
import jml2b.formula.Formula;
import jml2b.formula.IModifiesField;
import jml2b.formula.TerminalForm;
import jml2b.link.LinkContext;
import jml2b.link.LinkInfo;
import jml2b.pog.lemma.FormulaWithSpecMethodDecl;
import jml2b.pog.lemma.Goal;
import jml2b.pog.lemma.GoalOrigin;
import jml2b.pog.lemma.Proofs;
import jml2b.pog.lemma.SimpleLemma;
import jml2b.structure.AField;
import jml2b.structure.java.Class;
import jml2b.structure.java.Identifier;
import jml2b.structure.java.JmlFile;
import jml2b.structure.java.Parameters;
import jml2b.structure.java.ParsedItem;
import jml2b.structure.java.Type;
import jml2b.structure.statement.Expression;
import antlr.collections.AST;

/**
 * This class implements a <code>\nothing</code> modifies clause.
 * @author L. Burdy
 **/
public class ModifiesNothing extends ModifiesClause {

	/**
	 * Constructs a <code>\nothing</code> modifies clause corresponding to a 
	 * parsed item.
	 * @param jf The current JML file
	 * @param a The tree corresponding to this modifies
	 **/
	ModifiesNothing(JmlFile jf, AST a) throws Jml2bException {
		super(jf, a);
	}

	/**
	 * Constructs a <code>\nothing</code> modifies clause
	 */
	public ModifiesNothing() {
	}

	public Object clone() {
		return this;
	}

	public void instancie(IJml2bConfiguration config) {
	}

	public void instancie(Expression b, IJml2bConfiguration config) {
	}

	public LinkInfo linkStatements(IJml2bConfiguration config, LinkContext f)
		throws Jml2bException {
		return null;
	}

	public Type typeCheck(IJml2bConfiguration config, LinkContext f)
		throws Jml2bException {
		return null;
	}

	public void processIdent() {
	}

	/**
	 * @return <code>\nothing</code>
	 **/
	public String toJava(int indent) {
		return "\\nothing";
	}

	/**
	 * Returns the lemma corresponding to proof that all the fields and all the 
	 * array elements have not been modified.
	 * @return The lemmas corresponding to 
	 * <UL>
	 * <li> <code>f == \old(f)</code> for each static field
	 * <li> <code>\old(instances) <| f == \old(instances) <| \old(f)</code> for 
	 * each member field
	 * <li> <code>old(instances) <| xxxelements == \old(instances) <| 
	 * \old(xxxelements)</code> for each xxxelements variable.
	 * </UL>
	 **/
	public SimpleLemma modifiesLemmas(
		IJml2bConfiguration config,
		Vector fields,
		Vector nonModifiedFields,
		Formula[] nonModifiedxxxElements)
		throws PogException {
		// The set of calculated goals
		SimpleLemma res = new SimpleLemma();

		Enumeration e = fields.elements();
		Enumeration e1 = nonModifiedFields.elements();
		while (e.hasMoreElements()) {
			AField f = (AField) e.nextElement();
			Formula fo = new TerminalForm(new Identifier(f));
			fo.processIdent();
			Formula oldF = (Formula) e1.nextElement();
			if (f.getModifiers().isStatic()) {
				// for the static fields, add the goal f == \old(f)
				res.addGoal(
					new Goal(
						new FormulaWithSpecMethodDecl(new BinaryForm(Ja_EQUALS_OP, fo, oldF)),
						new GoalOrigin(GoalOrigin.MODIFIES, f)));
			} else {
				// for the member fields, add the goal 
				// \old(instances) <| f == \old(instances) <| \old(f)
				res.addGoal(
					new Goal(
						new FormulaWithSpecMethodDecl(new BinaryForm(EQUALS_ON_OLD_INSTANCES, fo, oldF)),
						new GoalOrigin(GoalOrigin.MODIFIES, f)));
			}
		}

		for (int i = 0; i < ElementsForm.elements.length; i++) {
			Formula fo = ElementsForm.elements[i];
			Formula oldF = nonModifiedxxxElements[i];

			// for all the xxxelements variable, add the goal
			// \old(instances) <| xxxelements 
			// == \old(instances) <| \old(xxxelements)
			res.addGoal(
				new Goal(
					new FormulaWithSpecMethodDecl(new BinaryForm(EQUALS_ON_OLD_INSTANCES_ARRAY, fo, oldF)),
					new GoalOrigin(GoalOrigin.MODIFIES)));
		}
		return res;
	}

	/**
	 * @return <code>this</code>
	 */
	public ModifiesClause renameParam(
		IJml2bConfiguration config,
		Parameters signature,
		Vector newSignature) {
		return this;
	}

	/**
	 * Performs no action
	 **/
	public void addDepends(IJml2bConfiguration config, Class c) {
	}

	/**
	 * Returns the proofs <code>s</code>, till no fields are modified
	 **/
	public Proofs modifies(
		IJml2bConfiguration config,
		IModifiesField m,
		Proofs s) {
		return s;
	};

	/**
	 * @return <code>l</code>
	 **/
	public ModifiesClause completeModifiesWithFields(ModifiesList l) {
		return l;
	}

	public void setParsedItem(ParsedItem pi) {
		change(pi);
	}

	static final long serialVersionUID = -2573792837984300742L;

}
