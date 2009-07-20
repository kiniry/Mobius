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
* This class implements a <code>do while</code> or a 
* <code>while do</code> loop statement
* @author L. Burdy
**/
class StDoWhile extends StLoops {

	/**
	 * The conditional expression
	 **/
	private Expression exp;

	/*@
	  @ invariant parsed ==> exp != null
	  @        && parsed ==> body != null
	  @        && parsed ==> exp.parsed
	  @        && parsed ==> body.parsed;
	  @*/

	/**
	 * Constructs a statement as a <i>parsed item</i>.
	 * @param jf The file where the statement is located
	 * @param tree The <code>AST</code> node corresponding to the statement
	 * @see jml2b.structure.java.ParsedItem#ParsedItem(JmlFile, AST)
	 **/
	protected StDoWhile(JmlFile jf, AST tree) {
		super(jf, tree);
	}

	public String emit() {
		switch (getNodeType()) {
			case LITERAL_do :
				return "do {\n"
					+ body.emit()
					+ "} while ("
					+ exp.toJava(0)
					+ ");\n";
			case LITERAL_while :
				return "while ("
					+ exp.toJava(0)
					+ ") {\n"
					+ body.emit()
					+ "}\n";
		}
		return null;
	}

	public AST parse(AST tree) throws Jml2bException {
		AST subtree = tree.getFirstChild();
		if (subtree.getFirstChild() != null) {
			parseModifies(getJmlFile(), subtree.getFirstChild());
		} /*else
			defaultLoop_modifies();*/
		subtree = subtree.getNextSibling();
		parseLoopInvariant(subtree);
		subtree = subtree.getNextSibling();
		parseLoopExsures(subtree);
		subtree = subtree.getNextSibling();
		parseLoopVariant(subtree);
		subtree = subtree.getNextSibling();
		switch (getNodeType()) {
			case LITERAL_do :
				body = Statement.createS(getJmlFile(), subtree);
				subtree = body.parse(subtree);
				exp = Expression.createE(getJmlFile(), subtree);
				subtree = exp.parse(subtree);
				break;
			case LITERAL_while :
				exp = Expression.createE(getJmlFile(), subtree);
				subtree = exp.parse(subtree);
				body = Statement.createS(getJmlFile(), subtree);
				subtree = body.parse(subtree);
				break;
			default :
				throw new Jml2bException("");
		}
		//@ set parsed = true;
		return tree.getNextSibling();
	}

	public LinkInfo linkStatement(IJml2bConfiguration config, LinkContext f)
		throws Jml2bException {
		super.linkStatement(config, f);
		body.linkStatement(config, f);
		exp.linkStatement(config, f);
		return null;
	}

	public Statement jmlNormalize(
		IJml2bConfiguration config,
		Class definingClass)
		throws PogException {
		super.jmlNormalize(config, definingClass);
		exp = (Expression) exp.jmlNormalize(config, definingClass);
		body = (Statement) body.jmlNormalize(config, definingClass);
		return this;
	}

	public Proofs wp(
		final IJml2bConfiguration config,
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
		ExceptionalBehaviourStack localExsuresStack = null;

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

			localExsuresStack =
				new ExceptionalBehaviourStack(
					new ExceptionalProofs(localExsures));

			exsures = localExsures.impliesExceptional(exceptionalBehaviour);
		}

		// Proof to prove at the initialization of the loop corresponding to the 
		// invariant
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
		Proofs init = new Proofs(initInv);

		// s = vv = TRUE: The stop condition is true. 
		BinaryForm s =
			new BinaryForm(
				Ja_EQUALS_OP,
				new TerminalForm(vv),
				new TerminalForm(Ja_LITERAL_true));

		Proofs st_0, st_1;
		Proofs st_2 = null;

		// st_0 is the proof of the invariant and the variant when the  
		// loop condition is true
		st_0 = new Proofs((SimpleLemma) invariant.clone());

		switch (getNodeType()) {
			case LITERAL_do :
				//TODO G?rer correctement les modified field dans le cas d'un do while

				st_0.addHyp(
					s,
					new ColoredInfo(exp, ColoredInfo.IS_TRUE),
					VirtualFormula.LOCALES);

				// st_1 is the proof of the normal behaviour when the loop 
				// condition is false
				st_1 = (Proofs) normalBehaviour.clone();
				st_1.addHyp(
					Formula.not(s),
					new ColoredInfo(exp, ColoredInfo.IS_FALSE),
					VirtualFormula.LOCALES);

				st_0.addAll(st_1);

				// st_2 is the conjunction of the two proofs where the loop 
				// condition has been evaluated. It corresponds to the normal
				// behaviour of the loop proof
				st_2 =
					exp.wp(
						config,
						vv,
						st_0,
						loopEx ? localExsuresStack : exceptionalBehaviour);

				// When the loop finishes on a break, the normal behaviour must 
				// be proved
				finishOnBreakLab.add(null, normalBehaviour);
				// When the loop terminates on a continue, the normal behaviour 
				// of the loop proof must be proved
				finishOnContinueLab.add(null, st_2);

				// The body is evaluated with the normal behaviour of the loop 
				// as normal behaviour
				st_2 =
					body.wp(
						config,
						st_2,
						finishOnReturn,
						finishOnBreakLab,
						finishOnContinueLab,
						loopEx ? localExsuresStack : exceptionalBehaviour);

				finishOnBreakLab.remove();
				finishOnContinueLab.remove();

				st_2.addHyp(
					getLoop_invariant().predToForm(config),
					new ColoredInfo(),
					VirtualFormula.LOOP_INVARIANT);

				//TODO Il ne faut pas supprimer les T_VARIANT_OLD qui etait present dans le normal behaviour mais uniquement ceux de la boucle courante
				st_2.suppressSpecialOld(IFormToken.T_VARIANT_OLD);
				st_2 = getLoop_modifies().modifies(config, this, st_2);

				break;

			case LITERAL_while :
				// When the loop finishes on a break, the normal behaviour must 
				// be proved
				finishOnBreakLab.add(null, normalBehaviour);

				// When the loop terminates on a continue, the invariant 
				// of the loop proof must be proved
				finishOnContinueLab.add(null, (Proofs) st_0.clone());

				// The body is evaluated with the invariant of the loop as 
				// normal behaviour
				st_0 =
					body.wp(
						config,
						st_0,
						finishOnReturn,
						finishOnBreakLab,
						finishOnContinueLab,
						loopEx ? localExsuresStack : exceptionalBehaviour);

				finishOnBreakLab.remove();
				finishOnContinueLab.remove();

				st_0.addHyp(
					s,
					new ColoredInfo(exp, ColoredInfo.IS_TRUE),
					VirtualFormula.LOCALES);

				Proofs st_3 =
					exp.wp(
						config,
						vv,
						st_0,
						loopEx ? localExsuresStack : exceptionalBehaviour);
				st_3.addHyp(
					getLoop_invariant().predToForm(config),
					new ColoredInfo(),
					VirtualFormula.LOOP_INVARIANT);

				st_3.suppressSpecialOld(IFormToken.T_VARIANT_OLD);
				st_3 =
					getLoop_modifies().modifies(
						config,
						new DuringLoop(line),
						st_3);

				// st_1 is the proof of the normal behaviour when the loop 
				// condition is false
				st_1 = (Proofs) normalBehaviour.clone();
				st_1.addHyp(
					Formula.not(s),
					new ColoredInfo(exp, ColoredInfo.IS_FALSE),
					VirtualFormula.LOCALES);

				st_2 =
					exp.wp(
						config,
						vv,
						st_1,
						loopEx ? localExsuresStack : exceptionalBehaviour);
				st_2.addHyp(
					getLoop_invariant().predToForm(config),
					new ColoredInfo(),
					VirtualFormula.LOOP_INVARIANT);

//				st_2.suppressSpecialOld(IFormToken.T_VARIANT_OLD);
				st_2 = getLoop_modifies().modifies(config, this, st_2);

				st_2.addAll(st_3);
				break;
		}

		Proofs st_3 = null;

		if (loopEx) {
			exsures.suppressSpecialOld(IFormToken.T_VARIANT_OLD);
			st_3 = getLoop_modifies().modifies(config, this, exsures);
		}

		st_2.suppressSpecialOld(IFormToken.T_CALLED_OLD);

		if (loopEx) {
			st_3.suppressSpecialOld(IFormToken.T_CALLED_OLD);
			st_2.addAll(st_3);
		}

		init.suppressSpecialOld(IFormToken.T_VARIANT_OLD);

		st_2.addAll(init);

		st_2.addAll(wellDef(config));

		st_2.addBox(new ColoredInfo(this, ColoredInfo.METHOD_CALL, getInfo()));

		return st_2;
	}

	public StLoops getLoopAtLine(int line) {
		if (getNodeType() == LITERAL_do
			&& line == body.firstStatement().getLine() + 1)
			return this;

		else if (line == getLine() + 1)
			return this;

		else
			return null;
	}

	/**
	 * Returns the conditional expression.
	 * @return <code>exp</code>
	 */
	Expression getExp() {
		return exp;
	}

	static final long serialVersionUID = 4201715476535858046L;

	/* (non-Javadoc)
	 * @see jml2b.structure.statement.Statement#getPrecondition(jml2b.util.ModifiableSet, java.util.Vector)
	 */
	public void getPrecondition(
		IJml2bConfiguration config,
		ModifiableSet modifies,
		Vector req,
		Vector ens)
		throws Jml2bException, PogException {
		exp.getPrecondition(config, modifies, req, ens);
		body.getPrecondition(config, modifies, req, ens);
	}

	public void collectCalledMethod(Vector calledMethod) {
		exp.collectCalledMethod(calledMethod);
		body.collectCalledMethod(calledMethod);
	}

	public void getAssert(Vector asser) {
		body.getAssert(asser);
	}

	public void getSpecBlock(Vector asser) {
		body.getSpecBlock(asser);
	}
	public void getLoop(Vector loops) {
		loops.add(this);
		body.getLoop(loops);
	}
}
