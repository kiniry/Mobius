//******************************************************************************
/* Copyright (c) 2002, 2003 GEMPLUS Software Research Labs. All Rights Reserved.
/* Copyright (c) 2003, 2004 INRIA. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: StSkip
/*
/*******************************************************************************
/* Warnings/Remarks:
/******************************************************************************/
package jml2b.structure.statement;

import java.util.Vector;

import jml2b.IJml2bConfiguration;
import jml2b.exceptions.Jml2bException;
import jml2b.link.LinkContext;
import jml2b.link.LinkInfo;
import jml2b.pog.lemma.ExceptionalBehaviourStack;
import jml2b.pog.lemma.LabeledProofsVector;
import jml2b.pog.lemma.Proofs;
import jml2b.structure.java.Class;
import jml2b.structure.java.JmlFile;
import jml2b.structure.java.Type;
import jml2b.util.ModifiableSet;
import antlr.collections.AST;

/**
 * This class implements a <code>skip</code> statement. This statement does not
 * exist in Java but it is usefull, for instance, to simulate empty operation 
 * body or end of a sequence list or the statement <code>;</code>.
 * @author L. Burdy, A. Requet
 **/
public class StSkip extends Statement {

	/**
	 * Constructs a <code>skip</code> statement.
	 **/
	public StSkip() {
		super();
	}

	/**
	 * Constructs a <code>skip</code> statement when a semi colon is parsed as a 
	 * statement.
	 **/
	StSkip(JmlFile jmlFile, AST tree) {
		super(jmlFile, tree);
	}

	public String emit() {
		return ";\n";
	}

	public AST parse(AST tree) {
		//@ set parsed = true;
		return tree.getNextSibling();
	}

	public LinkInfo linkStatement(IJml2bConfiguration config, LinkContext f)
		throws Jml2bException {
		return null;
	}

	public Type typeCheck(IJml2bConfiguration config, LinkContext f)
		throws Jml2bException {
		return null;
	}

	public Statement jmlNormalize(
		IJml2bConfiguration config,
		Class definingClass) {
		return this;
	}

	/**
	 * Returns the normal behaviour, till <code>skip</code> has no effect.
	 * @return <code>normalBehaviour</code>
	 **/
	public Proofs wp(
		IJml2bConfiguration config,
		Proofs normalBehaviour,
		Proofs finishOnReturn,
		LabeledProofsVector finishOnBreakLab,
		LabeledProofsVector finishOnContinueLab,
		ExceptionalBehaviourStack exceptionalBehaviour) {
		return (Proofs) normalBehaviour.clone();
	}

	public void getPrecondition(
		IJml2bConfiguration config,
		ModifiableSet modifies,
		Vector req,
		Vector ens) {
	}

	public void collectCalledMethod(Vector calledMethod) {
	}

	public void getAssert(Vector asser) {
	}

	public void getSpecBlock(Vector asser) {
	}

	public void getLoop(Vector asser) {
	}

	static final long serialVersionUID = 5018200138214163139L;

}
