//******************************************************************************
/* Copyright (c) 2002, 2003 GEMPLUS Software Research Labs. All Rights Reserved.
/* Copyright (c) 2003, 2004 INRIA. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: StBlock.java
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
import jml2b.pog.lemma.LabeledProofsVector;
import jml2b.pog.lemma.Proofs;
import jml2b.structure.java.JmlFile;
import jml2b.structure.java.Type;
import jml2b.structure.java.Class;
import jml2b.util.ModifiableSet;
import antlr.collections.AST;

/**
 * This class implements a block statement
 * @author L. Burdy
 **/
public class StBlock extends Statement {

	/**
	 * The encapsulated statement
	 **/
	private Statement body;

	/*@
	  @ invariant parsed ==> body != null;
	  @*/

	/**
	 * Constructs a statement that will be filled by the parse method.
	 * @param jf The parsed file
	 * @param tree The current tree node
	 **/
	protected StBlock(JmlFile jf, AST tree) {
		super(jf, tree);
	}

	public String emit() {
		return "{\n" + body.emit() + "}\n";
	}

	/*@
	  @ modifies body;
	  @ ensures body != null;
	  @*/
	public AST parse(AST tree) throws Jml2bException {
		if (tree.getNextSibling().getType() == RCURLY) {
			body = new StSkip();
			return tree.getNextSibling().getNextSibling();
		}
		body = new StSequence(getJmlFile(), tree.getNextSibling());
		//@ set parsed = true;
		return body.parse(tree.getNextSibling());
	}

	public LinkInfo linkStatement(IJml2bConfiguration config, LinkContext f)
		throws Jml2bException {
		// create new local variables
		f.linkVars.pushVars();
		body.linkStatement(config, f);
		// remove the local variables
		f.linkVars.popVars();
		return null;
	}

	public Type typeCheck(IJml2bConfiguration config, LinkContext f)
		throws Jml2bException {
		// create new local variables
		f.linkVars.pushVars();
		body.typeCheck(config, f);
		// remove the local variables
		f.linkVars.popVars();
		return null;
	}

	public Statement jmlNormalize(
		IJml2bConfiguration config,
		Class definingClass)
		throws PogException {
		body = (Statement) body.jmlNormalize(config, definingClass);
		return this;
	}

	public Statement firstStatement() {
		return body.firstStatement();
	}

	public Statement tail() {
		return body.tail();
	}

	/**
	 * Applies the encapsulated statement on the current proof context.
	 **/
	public Proofs wp(
		IJml2bConfiguration config,
		Proofs normalBehaviour,
		Proofs finishOnReturn,
		LabeledProofsVector finishOnBreakLab,
		LabeledProofsVector finishOnContinueLab,
		ExceptionalBehaviourStack exceptionalBehaviour)
		throws Jml2bException, PogException {
		return body.wp(
			config,
			normalBehaviour,
			finishOnReturn,
			finishOnBreakLab,
			finishOnContinueLab,
			exceptionalBehaviour);
	}

	public StLoops getLoopAtLine(int line) {
		return body.getLoopAtLine(line);
	}

	static final long serialVersionUID = 7877759894682929151L;

	/**
	 * @return
	 */
	public Statement getBody() {
		return body;
	}

	public void getPrecondition(
		IJml2bConfiguration config,
		ModifiableSet modifies,
		Vector req,
		Vector ens)
		throws Jml2bException, PogException {
		body.getPrecondition(config, modifies, req, ens);
	}
	public void collectCalledMethod(Vector calledMethod) {
		body.collectCalledMethod(calledMethod);
	}

	public void getAssert(Vector asser) {
		body.getAssert(asser);
	}
	
	public void getSpecBlock(Vector asser) {
		body.getSpecBlock(asser);
	}
	
	public void getLoop(Vector asser) {
		body.getLoop(asser);
	}

}
