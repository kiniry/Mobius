//******************************************************************************
/* Copyright (c) 2002, 2003 GEMPLUS Software Research Labs. All Rights Reserved.
/* Copyright (c) 2003, 2004 INRIA. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: StSequence.java
/*
/*******************************************************************************
/* Warnings/Remarks:
/******************************************************************************/
package jml2b.structure.statement;

import java.util.Vector;

import jml2b.IJml2bConfiguration;
import jml2b.exceptions.Jml2bException;
import jml2b.exceptions.PogException;
import jml2b.link.LinkContext;
import jml2b.link.LinkInfo;
import jml2b.pog.lemma.ExceptionalBehaviourStack;
import jml2b.pog.lemma.LabeledProofsVector;
import jml2b.pog.lemma.Proofs;
import jml2b.structure.java.Class;
import jml2b.structure.java.JmlFile;
import jml2b.structure.java.ParsedItem;
import jml2b.structure.java.Type;
import jml2b.util.ModifiableSet;
import antlr.collections.AST;

/**
 * This class implements a sequence of two statements.
 * @author L. Burdy, A. Requet
 **/
public class StSequence extends Statement {

	/**
	 * The first statement
	 **/
	private Statement left;

	/**
	 * The second statement. It is never null. It can be <code>skip</code>.
	 **/
	private Statement right;

	/*@
	  @ invariant parsed ==> left != null
	  @        && parsed ==> right != null
	  @        && parsed ==> left.parsed
	  @        && parsed ==> right.parsed;
	  @*/

	/**
	 * Construct an empty statement that will be filled during the parse
	 * @param jf The JML file
	 * @param tree The current AST tree node
	 **/
	protected StSequence(JmlFile jf, AST tree) {
		super(jf, tree);
	}

	protected StSequence(ParsedItem pi) {
		super(pi);
	}

	public String emit() {
		return left.emit() + right.emit();
	}

	/**
	 * Constructs a sequence from another one.
	 * @param pi The parsed item
	 * @param left The first statement
	 * @param right The second statement
	 **/
	/*@
	  @ requires left != null;
	  @*/
	public StSequence(ParsedItem pi, Statement left, Statement right) {
		super(pi);
		this.left = left;
		if (right == null)
			this.right = new StSkip();
		else
			this.right = right;
		//@ set parsed = true;
	}

	/*@
	  @ modifies left, right;
	  @ ensures left != null && right != null;
	  @*/
	public AST parse(AST tree) throws Jml2bException {
		AST subtree;
		left = Statement.createS(getJmlFile(), tree);
		subtree = left.parse(tree);
		if (subtree == null) {
			right = new StSkip();
			return null;
		} else {
			if (subtree.getType() == RCURLY) {
				right = new StSkip();
				return subtree.getNextSibling();
			} else {
				right = new StSequence(getJmlFile(), subtree);
				return right.parse(subtree);
			}
		}
		//@ set parsed = true;
	}

	public LinkInfo linkStatement(IJml2bConfiguration config, LinkContext f)
		throws Jml2bException {
		left.linkStatement(config, f);
		right.linkStatement(config, f);
		return null;
	}

	public Type typeCheck(IJml2bConfiguration config, LinkContext f)
		throws Jml2bException {
		left.typeCheck(config, f);
		right.typeCheck(config, f);
		return null;
	}

	public Statement jmlNormalize(
		IJml2bConfiguration config,
		Class definingClass)
		throws PogException {
		left = (Statement) left.jmlNormalize(config, definingClass);
		right = (Statement) right.jmlNormalize(config, definingClass);
		return this;
	}

	/**
	 * @return the first statement of the first statement
	 **/
	public Statement firstStatement() {
		return left.firstStatement();
	}

	/**
	 * @return the second statement
	 **/
	public Statement tail() {
		Statement t;
		if ((t = left.tail()) != null)
			return new StSequence(this, t, right);
		else
			return right;
	}

	/**
	 * Calculates the second statement on the proof context and then the first
	 * with the resulting proof as normal behaviour.
	 * @throws PogException when an OutOfMemory occurs during the calculus.
	 **/
	public Proofs wp(
		IJml2bConfiguration config,
		Proofs normalBehaviour,
		Proofs finishOnReturn,
		LabeledProofsVector finishOnBreakLab,
		LabeledProofsVector finishOnContinueLab,
		ExceptionalBehaviourStack exceptionalBehaviour)
		throws Jml2bException, PogException {
		try {
			return left.wp(
				config,
				right.wp(
					config,
					normalBehaviour,
					finishOnReturn,
					finishOnBreakLab,
					finishOnContinueLab,
					exceptionalBehaviour),
				finishOnReturn,
				finishOnBreakLab,
				finishOnContinueLab,
				exceptionalBehaviour);
		} catch (OutOfMemoryError oome) {
			// Try to garbage memory and to return a PogException that will
			// lead to a message in the task list.
			normalBehaviour = null;
			finishOnReturn = null;
			finishOnBreakLab = null;
			finishOnContinueLab = null;
			exceptionalBehaviour = null;
			Runtime.getRuntime().gc();

			throw new PogException("OutOfMemoryError", this);
		}
	}

	public StLoops getLoopAtLine(int line) {
		StLoops res = left.getLoopAtLine(line);
		if (res == null)
			return right.getLoopAtLine(line);
		else
			return res;
	}

	public void getPrecondition(
		IJml2bConfiguration config,
		ModifiableSet modifies,
		Vector req,
		Vector ens)
		throws Jml2bException, PogException {
		left.getPrecondition(config, modifies, req, ens);
		right.getPrecondition(config, modifies, req, ens);
	}

	public void collectCalledMethod(Vector calledMethod) {
		left.collectCalledMethod(calledMethod);
		right.collectCalledMethod(calledMethod);
	}

	public void getAssert(Vector asser) {
		left.getAssert(asser);
		right.getAssert(asser);
	}
	
	public void getSpecBlock(Vector asser) {
		left.getSpecBlock(asser);
		right.getSpecBlock(asser);
	}
	
	public void getLoop(Vector asser) {
		left.getLoop(asser);
		right.getLoop(asser);
	}
	
	static final long serialVersionUID = 3977087978296856377L;

}
