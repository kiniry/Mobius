//******************************************************************************
/* Copyright (c) 2002, 2003 GEMPLUS Software Research Labs. All Rights Reserved.
/* Copyright (c) 2003, 2004 INRIA. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: 
/*
/*******************************************************************************
/* Warnings/Remarks:
/******************************************************************************/

package jml2b.structure.statement;

import java.util.Vector;

import jml2b.IJml2bConfiguration;
import jml2b.exceptions.Jml2bException;
import jml2b.exceptions.PogException;
import jml2b.formula.BinaryForm;
import jml2b.formula.Formula;
import jml2b.formula.IFormToken;
import jml2b.formula.TerminalForm;
import jml2b.link.LinkContext;
import jml2b.link.LinkInfo;
import jml2b.pog.lemma.ExceptionalBehaviourStack;
import jml2b.pog.lemma.ExceptionalProofs;
import jml2b.pog.lemma.FormulaWithSpecMethodDecl;
import jml2b.pog.lemma.GoalOrigin;
import jml2b.pog.lemma.LabeledProofsVector;
import jml2b.pog.lemma.Proofs;
import jml2b.pog.lemma.SimpleLemma;
import jml2b.pog.lemma.Theorem;
import jml2b.pog.lemma.VariantLemma;
import jml2b.pog.lemma.VirtualFormula;
import jml2b.pog.util.ColoredInfo;
import jml2b.structure.java.JmlFile;
import jml2b.structure.java.Class;
import jml2b.structure.jml.SpecCase;
import jml2b.util.ModifiableSet;
import antlr.collections.AST;

/**
 * @author lburdy
 *
 * To change the template for this generated type comment go to
 * Window&gt;Preferences&gt;Java&gt;Code Generation&gt;Code and Comments
 */
public /**
* This class implements a for statement
* @author L. Burdy
**/
class StFor extends StLoops {

	/**
	 * The initialization statement of the loop
	 **/
	private Statement init;

	/**
	 * The test statement of the loop
	 **/
	private Expression test;

	/**
	 * The updater statement of the loop
	 **/
	private Statement updater;

	/*@
	  @ invariant parsed ==> init != null
	  @        && parsed ==> test != null
	  @        && parsed ==> updater != null
	  @        && parsed ==> body != null
	  @        && parsed ==> init.parsed
	  @        && parsed ==> test.parsed
	  @        && parsed ==> updater.parsed
	  @        && parsed ==> body.parsed;
	  @*/

	/**
	 * Constructs a statement as a <i>parsed item</i>.
	 * @param jf The file where the statement is located
	 * @param tree The <code>AST</code> node corresponding to the statement
	 * @see jml2b.structure.java.ParsedItem#ParsedItem(JmlFile, AST)
	 **/
	protected StFor(JmlFile jf, AST tree) {
		super(jf, tree);
	}

	public String emit() {
		return "for("
			+ init.emit()
			+ test.toJava(0)
			+ ";"
			+ updater.emit()
			+ ") {\n"
			+ body.emit()
			+ "}\n";
	}

	public AST parse(AST tree) throws Jml2bException {
		AST subtree = tree.getFirstChild();

		// Parses the initialization of the loop
		if (subtree.getFirstChild() != null) {
			init = Statement.createS(getJmlFile(), subtree.getFirstChild());
			init.parse(subtree.getFirstChild());
		} else
			init = new StSkip();

		// Parses the loop condition
		subtree = subtree.getNextSibling();
		if (subtree.getFirstChild() != null) {
			test = Expression.createE(getJmlFile(), subtree.getFirstChild());
			test.parse(subtree.getFirstChild());
		} else
			test = new TerminalExp(BTRUE, "(0=0)");

		// Parses the updater of the loop
		subtree = subtree.getNextSibling();
		if (subtree.getFirstChild() != null) {
			updater = Statement.createS(getJmlFile(), subtree.getFirstChild());
			updater.parse(subtree.getFirstChild());
		} else
			updater = new StSkip();

		// Parses the loop modifies clause
		subtree = subtree.getNextSibling();
		if (subtree.getFirstChild() != null) {
			parseModifies(getJmlFile(), subtree.getFirstChild());
		} /*else
					defaultLoop_modifies();*/

		// Parses the loop invariant
		subtree = subtree.getNextSibling();
		parseLoopInvariant(subtree);

		// Parses the loop exsures
		subtree = subtree.getNextSibling();
		parseLoopExsures(subtree);

		// Parses the variant
		subtree = subtree.getNextSibling();
		parseLoopVariant(subtree);

		// Parses the body of the loop
		subtree = subtree.getNextSibling();
		body = Statement.createS(getJmlFile(), subtree);
		body.parse(subtree);
		//@ set parsed = true;
		return tree.getNextSibling();
	}

	public LinkInfo linkStatement(IJml2bConfiguration config, LinkContext f)
		throws Jml2bException {
		// Push a new local variable context
		f.linkVars.pushVars();

		// Links the initialization
		init.linkStatement(config, f);

		// Links the test
		test.linkStatement(config, f);

		// Links the updater
		updater.linkStatement(config, f);

		// Links the loop specification
		super.linkStatement(config, f);

		// Links the body
		body.linkStatement(config, f);

		// Pop the local variable context
		f.linkVars.popVars();
		return null;
	}

	public Statement jmlNormalize(
		IJml2bConfiguration config,
		Class definingClass)
		throws PogException {
		super.jmlNormalize(config, definingClass);
		init = (Statement) init.jmlNormalize(config, definingClass);
		test = (Expression) test.jmlNormalize(config, definingClass);
		updater = (Statement) updater.jmlNormalize(config, definingClass);
		body = (Statement) body.jmlNormalize(config, definingClass);
		return this;
	}

	public Proofs wp(
		IJml2bConfiguration config,
		Proofs normalBehaviour,
		Proofs finishOnReturn,
		LabeledProofsVector finishOnBreakLab,
		LabeledProofsVector finishOnContinueLab,
		ExceptionalBehaviourStack exceptionalBehaviour)
		throws Jml2bException, PogException {
		//TODO G?n?rer les lemmes pour v?rifier les loop_modifies

		// vv is a temporary variable corresponding to the result of the 
		// evaluation of the loop stop condition.
		String vv = fresh();

		Expression invariantE = (Expression) getLoop_invariant().clone();
		invariantE.old();
		FormulaWithSpecMethodDecl invariantF = invariantE.predToForm(config);

		// The lemma corresponding to the invariant of the loop.
		SimpleLemma invariant =
			new SimpleLemma(
				config,
				getLoop_invariant(),
				new GoalOrigin(GoalOrigin.LOOP_INVARIANT_PRESERVE));
		if (getLoop_variant() != null)
			invariant.addGoals(new VariantLemma(config, getLoop_variant()));

		// Check whether the loop declares an exceptional behaviour.
		boolean loopEx = getLoop_exsures().size() != 0;

		// Exceptional proofs stack corresponding to the loop exsures. It is 
		// valid only when loopEx is true.
		ExceptionalBehaviourStack localExsuresVector = null;

		// Proof corresponding to the fact that the loop exsures implies the
		// current exceptional behaviour stack. It is valid only when 
		// loopEx is true.
		Proofs exsures = null;
		if (loopEx) {
			// JML normalize the loop exsures.
			SpecCase.exsureVectorInstancie(getLoop_exsures().elements());

			// Theorem corresponding to the loop exsures
			Theorem localExsures =
				new Theorem(
					config,
					getLoop_exsures().elements(),
					null,
					new GoalOrigin(GoalOrigin.LOOP_EXSURES));

			localExsuresVector =
				new ExceptionalBehaviourStack(
					new ExceptionalProofs(localExsures));

			exsures = localExsures.impliesExceptional(exceptionalBehaviour);

		}

		SimpleLemma initInv =
			new SimpleLemma(
				config,
				getLoop_invariant(),
				new GoalOrigin(GoalOrigin.LOOP_INVARIANT_INIT));
		if (getLoop_variant() != null)
			initInv.addGoals(
				new SimpleLemma(
					config,
					new BinaryExp(
						RELATIONAL_OP,
						getLoop_variant(),
						">=",
						new TerminalExp(NUM_INT, "0")),
					new GoalOrigin(GoalOrigin.LOOP_VARIANT)));

		// Initialization lemma
		Proofs st_5 =
			init.wp(
				config,
				new Proofs(initInv),
				finishOnReturn,
				finishOnBreakLab,
				finishOnContinueLab,
				exceptionalBehaviour);

		// s = vv == true
		BinaryForm s =
			new BinaryForm(
				Ja_EQUALS_OP,
				new TerminalForm(vv),
				new TerminalForm(Ja_LITERAL_true));

		// proofs that the upadter establish the invariant
		Proofs st_4 =
			updater.wp(
				config,
				new Proofs(invariant),
				finishOnReturn,
				finishOnBreakLab,
				finishOnContinueLab,
				loopEx ? localExsuresVector : exceptionalBehaviour);

		// If the body terminates with a break, the normal behaviour should be 
		// ensured
		finishOnBreakLab.add(null, normalBehaviour);

		// If the body terminates on a continue, the proof that the updater
		// establish the invariant should be ensured.
		finishOnContinueLab.add(null, st_4);

		// proofs that the body establish that the updater establish the 
		// invariant
		Proofs st_1 =
			body.wp(
				config,
				(Proofs) st_4.clone(),
				finishOnReturn,
				finishOnBreakLab,
				finishOnContinueLab,
				loopEx ? localExsuresVector : exceptionalBehaviour);

		// Removes the break and continue proofs
		finishOnBreakLab.remove();
		finishOnContinueLab.remove();

		// Add the hypothese that the loop condition is true
		st_1.addHyp(
			s,
			new ColoredInfo(test, ColoredInfo.IS_TRUE),
			VirtualFormula.LOCALES);

		// Evaluates the proof condition
		Proofs st_11 =
			test.wp(
				config,
				vv,
				st_1,
				loopEx ? localExsuresVector : exceptionalBehaviour);

		// Adds the loop invariant in hypothesis        
		st_11.addHyp(
			invariantF,
			new ColoredInfo(getLoop_invariant()),
			VirtualFormula.LOOP_INVARIANT);

		// Quantify on modified variable
		st_11.suppressSpecialOld(IFormToken.T_VARIANT_OLD);
		st_11 =
			getLoop_modifies().modifies(config, new DuringLoop(line), st_11);

		// Proofs of the normal behaviour when the loop condition is false
		Proofs st_0 = (Proofs) normalBehaviour.clone();
		st_0.addHyp(
			Formula.not(s),
			new ColoredInfo(test, ColoredInfo.IS_FALSE),
			VirtualFormula.LOCALES);

		// Evaluates the proof condition
		Proofs st_01 =
			test.wp(
				config,
				vv,
				st_0,
				loopEx ? localExsuresVector : exceptionalBehaviour);

		// Adds the loop invariant in hypothesis        
		st_01.addHyp(
			invariantF,
			new ColoredInfo(getLoop_invariant()),
			VirtualFormula.LOOP_INVARIANT);

		// Quantify on modified variable
//		st_01.suppressSpecialOld(IFormToken.T_VARIANT_OLD);
		st_01 = getLoop_modifies().modifies(config, this, st_01);

		st_01.addAll(st_11);

		Proofs st_3 = null;

		if (loopEx) {
			exsures.suppressSpecialOld(IFormToken.T_VARIANT_OLD);
			st_3 = getLoop_modifies().modifies(config, this, exsures);
		}

		st_01.suppressSpecialOld(IFormToken.T_CALLED_OLD);
		if (loopEx) {
			st_3.suppressSpecialOld(IFormToken.T_CALLED_OLD);
			st_01.addAll(st_3);
		}

		st_5.suppressSpecialOld(IFormToken.T_VARIANT_OLD);

		st_01.addAll(st_5);

		st_01.addAll(wellDef(config));

		st_01.addBox(new ColoredInfo(this, ColoredInfo.METHOD_CALL, getInfo()));

		return st_01;
	}

	/**
	 * Returns the updater statement.
	 * @return <code>updater</code>
	 */
	public Statement getUpdater() {
		return updater;
	}

	public StLoops getLoopAtLine(int line) {
		if (line == test.getLine() + 1)
			return this;
		else
			return null;
	}

	static final long serialVersionUID = -2170236617582111769L;

	public void getPrecondition(
		IJml2bConfiguration config,
		ModifiableSet modifies,
		Vector req,
		Vector ens)
		throws Jml2bException, PogException {
		init.getPrecondition(config, modifies, req, ens);
		body.getPrecondition(config, modifies, req, ens);
		test.getPrecondition(config, modifies, req, ens);
		updater.getPrecondition(config, modifies, req, ens);
	}

	public void collectCalledMethod(Vector calledMethod) {
		init.collectCalledMethod(calledMethod);
		body.collectCalledMethod(calledMethod);
		test.collectCalledMethod(calledMethod);
		updater.collectCalledMethod(calledMethod);
	}

	public void getAssert(Vector asser) {
		init.getAssert(asser);
		body.getAssert(asser);
		updater.getAssert(asser);
	}

	public void getSpecBlock(Vector asser) {
		init.getSpecBlock(asser);
		body.getSpecBlock(asser);
		updater.getSpecBlock(asser);
	}
	
	public void getLoop(Vector loops) {
		loops.add(this);
		init.getLoop(loops);
		body.getLoop(loops);
		updater.getLoop(loops);
	}
}
