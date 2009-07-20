//******************************************************************************
/* Copyright (c) 2002, 2003 GEMPLUS Software Research Labs. All Rights Reserved.
 /* Copyright (c) 2003, 2004 INRIA. All Rights Reserved.
 /*------------------------------------------------------------------------------
 /* Name: StAssert.java
 /*
 /*******************************************************************************
 /* Warnings/Remarks:
 /*  09/26/2003 : Simplify integration achieved
 /******************************************************************************/

package jml2b.structure.statement;

import java.util.Vector;

import jml2b.IJml2bConfiguration;
import jml2b.exceptions.Jml2bException;
import jml2b.exceptions.PogException;
import jml2b.link.LinkContext;
import jml2b.link.LinkInfo;
import jml2b.pog.lemma.ExceptionalBehaviourStack;
import jml2b.pog.lemma.GoalOrigin;
import jml2b.pog.lemma.LabeledProofsVector;
import jml2b.pog.lemma.Proofs;
import jml2b.pog.lemma.SimpleLemma;
import jml2b.pog.lemma.Theorem;
import jml2b.pog.lemma.VirtualFormula;
import jml2b.pog.util.ColoredInfo;
import jml2b.structure.java.JmlFile;
import jml2b.structure.java.Type;
import jml2b.structure.java.Class;
import jml2b.util.ModifiableSet;
import antlr.collections.AST;

/**
 * @author lburdy
 *
 * To change the template for this generated type comment go to
 * Window&gt;Preferences&gt;Java&gt;Code Generation&gt;Code and Comments
 */
public/**
		   * This class implements an assert statement.
		   * 
		   * @author L. Burdy
		   */
class StAssert extends Statement {

	/**
	 * The asserted predicate
	 */
	private Expression exp;

	/*
	 * @ @ invariant parsed ==> exp != null; @
	 */

	/**
	 * Constructs a statement that will be filled by the parse method.
	 * 
	 * @param jf
	 *                    The parsed file
	 * @param tree
	 *                    The current tree node
	 */
	protected StAssert(JmlFile jf, AST tree) {
		super(jf, tree);
	}

	/**
	 * @param exp
	 */
	StAssert(TerminalExp exp) {
		this.exp = exp;
	}

	public String emit() {
		return "/*@ assert " + exp.toJava(0) + ";@*/\n";
	}

	/**
	 * Parses the assert statement.
	 */
	/*
	 * @ @ modifies exp; @ ensures exp != null; @
	 */
	public AST parse(AST tree) throws Jml2bException {
		// exp can alredy exists when an assert is created from an unreachable
		// statement.
		if (exp == null) {
			exp = Expression.createE(getJmlFile(), tree.getFirstChild());
			exp.parse(tree.getFirstChild());
		}
		//@ set parsed = true;
		return tree.getNextSibling();
	}

	/**
	 * Links the asserted predicate
	 */
	public LinkInfo linkStatement(IJml2bConfiguration config, LinkContext f) throws Jml2bException {
		exp.linkStatement(config, f);
		return null;
	}

	public Type typeCheck(IJml2bConfiguration config, LinkContext f) throws Jml2bException {
		return exp.typeCheck(config, f);
	}

	public Statement jmlNormalize(IJml2bConfiguration config, Class definingClass) {
		exp = (Expression) exp.jmlNormalize(config, definingClass);
		return this;
	}

	/**
	 * Adds the asserted predicate in hypothesis of the current normal behaviour
	 * proof and adds a new proof corresponding to the proof of the assertion.
	 */
	public Proofs wp(IJml2bConfiguration config, Proofs normalBehaviour, Proofs finishOnReturn,
			LabeledProofsVector finishOnBreakLab, LabeledProofsVector finishOnContinueLab,
			ExceptionalBehaviourStack exceptionalBehaviour) throws Jml2bException, PogException {
		Proofs res = (Proofs) normalBehaviour.clone();
		res.addHyp(exp.predToForm(config), new ColoredInfo(this), VirtualFormula.ASSERT);
		res.addAll(new Proofs(new SimpleLemma(config, exp, new GoalOrigin(GoalOrigin.ASSERT))));
		if (config.isWellDefPoGenerated())
			res.addAll(exp.ensures(	config,
									Theorem.getTrue(config),
									ExceptionalBehaviourStack.getFalse(config),
									new Vector()));
		return res;
	}

	static final long serialVersionUID = -3959347360206595623L;

	public void getPrecondition(IJml2bConfiguration config, ModifiableSet modifies, Vector req, Vector ens) {
	}

	public void collectCalledMethod(Vector calledMethod) {
	}

	public Expression getExp() {
		return exp;
	}

	public void getAssert(Vector asser) {
		asser.add(this);
	}

	public void getSpecBlock(Vector asser) {
	}
	public void getLoop(Vector asser) {
	}

}

