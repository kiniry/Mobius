//******************************************************************************
/* Copyright (c) 2002, 2003 GEMPLUS Software Research Labs. All Rights Reserved.
/* Copyright (c) 2003, 2004 INRIA. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: StSpecBlock
/*
/*******************************************************************************
/* Warnings/Remarks:
/******************************************************************************/
package jml2b.structure.statement;

import java.util.Vector;

import jml.LineAST;
import jml2b.IJml2bConfiguration;
import jml2b.exceptions.Jml2bException;
import jml2b.exceptions.PogException;
import jml2b.formula.IFormToken;
import jml2b.formula.IModifiesField;
import jml2b.link.LinkContext;
import jml2b.link.LinkInfo;
import jml2b.pog.lemma.ExceptionalBehaviourStack;
import jml2b.pog.lemma.ExceptionalProofs;
import jml2b.pog.lemma.GoalOrigin;
import jml2b.pog.lemma.LabeledProofsVector;
import jml2b.pog.lemma.Proofs;
import jml2b.pog.lemma.SimpleLemma;
import jml2b.pog.lemma.Theorem;
import jml2b.pog.lemma.VirtualFormula;
import jml2b.pog.util.ColoredInfo;
import jml2b.structure.java.Class;
import jml2b.structure.java.JmlFile;
import jml2b.structure.java.Type;
import jml2b.structure.jml.SpecCase;
import jml2b.util.ModifiableSet;
import antlr.collections.AST;

/**
 * This class implements a specified block. It corresponds to a block prefixed 
 * with a JML lightweight specification. This expression has been added to the 
 * JML syntax. It allows to cut proof obligation generation process by 
 * simulating a method call.
 * @author L. Burdy, A. Requet
 **/
public class StSpecBlock extends Statement implements IModifiesField {

	/**
	 * The JML specification of the block
	 **/
	private SpecCase sp;

	/**
	 * The block statement
	 **/
	private StBlock block;

	private int startLine;
	private int endLine;

	/*@
	  @ private invariant sp != null;
	  @ invariant parsed ==> block != null
	  @        && parsed ==> block.parsed;
	  @*/

	/**
	 * Constructs a specified block as a <i>parsed item</i>.
	 * @param jf The file where the statement is located
	 * @param tree The <code>AST</code> node corresponding to the statement
	 * @see jml2b.structure.java.ParsedItem#ParsedItem(JmlFile, AST)
	 **/
	protected StSpecBlock(JmlFile jf, AST tree) throws Jml2bException {
		super(jf, tree);
		sp = new SpecCase(jf.getConfig());
		startLine = ((LineAST) tree.getFirstChild()).line;
		if (tree.getNextSibling() != null)
			endLine = ((LineAST) tree.getNextSibling()).line;
		else
			endLine = -1;
	}

	public String emit() {
		return sp.emit(null) + "{\n" + block.emit() + "}\n";
	}

	public AST parse(AST tree) throws Jml2bException {
		//@ set parsed = true;
		AST current = sp.parseSpecBlock(getJmlFile(), tree.getFirstChild());
		block = new StBlock(getJmlFile(), current);
		block.parse(current);
		return tree.getNextSibling();
	}

	public LinkInfo linkStatement(IJml2bConfiguration config, LinkContext f)
		throws Jml2bException {
		sp.link(config, f);
		sp.linkStatements(config, f);
		return block.linkStatement(config, f);
	}

	public Type typeCheck(IJml2bConfiguration config, LinkContext f)
		throws Jml2bException {
		sp.typeCheck(config, f);
		block.typeCheck(config, f);
		return null;
	}

	public Statement jmlNormalize(
		IJml2bConfiguration config,
		Class definingClass)
		throws PogException {
		sp.jmlNormalize(config, definingClass);
		block = (StBlock) block.jmlNormalize(config, definingClass);
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

		// proof of the requires of the specified block.
		SimpleLemma requires =
			new SimpleLemma(
				config,
				sp.getRequires(),
				new GoalOrigin(GoalOrigin.BLOCK_REQUIRES));

		Theorem localExsures =
			new Theorem(
				config,
				sp.getExsures(),
				null,
				new GoalOrigin(GoalOrigin.BLOCK_EXSURES));

		ExceptionalBehaviourStack localExsuresVector =
			new ExceptionalBehaviourStack(new ExceptionalProofs(localExsures));

		// proof that the exsures implies the current exceptionnal behaviour.
		Proofs exsures = localExsures.impliesExceptional(exceptionalBehaviour);

		// proof that the ensures implies the current normal behaviour.
		Proofs ensures = (Proofs) normalBehaviour.clone();
		ensures.addHyp(
			sp.getEnsures().predToForm(config),
			new ColoredInfo(sp.getEnsures()),
			VirtualFormula.BLOCK_ENSURES);

		Proofs st_1 =
			new Proofs(
				new SimpleLemma(
					config,
					sp.getEnsures(),
					new GoalOrigin(GoalOrigin.BLOCK_ENSURES)));

		// proof that the block implements its specification: the ensures and
		// the exsures.
		st_1 =
			block.wp(
				config,
				st_1,
				finishOnReturn,
				finishOnBreakLab,
				finishOnContinueLab,
				localExsuresVector);

		// Quantify on modified variables
		if (sp.getModifies() != null) {
			st_1 = sp.getModifies().modifies(config, this, st_1);
			ensures = sp.getModifies().modifies(config, this, ensures);
			exsures = sp.getModifies().modifies(config, this, exsures);
		}

		// Adds the requires in hypothesis
		st_1.addHyp(requires, VirtualFormula.REQUIRES);

		st_1.addAll(ensures);
		st_1.addAll(exsures);

		st_1.suppressSpecialOld(IFormToken.T_CALLED_OLD);

		// Proofs of the requires clause of the specified block
		st_1.addAll(new Proofs(requires));

		st_1.addAll(
			sp.getRequires().ensures(
				config,
				Theorem.getTrue(config),
				ExceptionalBehaviourStack.getFalse(config),
				new Vector()));

		Proofs st_2 =
			sp.getNormalizedEnsures().ensures(
				config,
				Theorem.getTrue(config),
				ExceptionalBehaviourStack.getFalse(config),
				new Vector());

		st_2.addAll(
			sp.getExsuresAsExpression().ensures(
				config,
				Theorem.getTrue(config),
				ExceptionalBehaviourStack.getFalse(config),
				new Vector()));
		st_2.addHyp(sp.getRequires().exprToForm(config));
		st_1.addAll(st_2);

		return st_1;
	}

	public String getNameForModifies() {
		return "after specified block at line " + startLine;
	}

	public void getPrecondition(
		IJml2bConfiguration config,
		ModifiableSet modifies,
		Vector req,
		Vector ens)
		throws Jml2bException, PogException {
		block.getPrecondition(config, modifies, req, ens);
	}

	public void collectCalledMethod(Vector calledMethod) {
		block.collectCalledMethod(calledMethod);
	}

	public void getAssert(Vector asser) {
		block.getAssert(asser);
	}
	
	public void getSpecBlock(Vector asser) {
		block.getSpecBlock(asser);
		asser.add(this);
	}
	
	public void getLoop(Vector asser) {
		block.getLoop(asser);
	}
	
	static final long serialVersionUID = 1332238792450955606L;

	/**
	 * @return
	 */
	public SpecCase getSp() {
		return sp;
	}

	/**
	 * @return
	 */
	public int getEndLine() {
		return endLine;
	}

	/**
	 * @return
	 */
	public int getStartLine() {
		return startLine;
	}

}
