//******************************************************************************
/* Copyright (c) 2002, 2003 GEMPLUS Software Research Labs. All Rights Reserved.
/* Copyright (c) 2003, 2004 INRIA. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: StImplementsLabel
/*
/*******************************************************************************
/* Warnings/Remarks:
/******************************************************************************/
package jml2b.structure.statement;

import java.util.Enumeration;
import java.util.Vector;

import jml2b.IJml2bConfiguration;
import jml2b.exceptions.Jml2bException;
import jml2b.exceptions.PogException;
import jml2b.exceptions.WrongLabelException;
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
 * This class implements an <i>implements label</i> statement. This statement 
 * allows to signal which labels are possibly implemented by a branch in the 
 * code.
 * @author L. Burdy
 **/
public class StImplementsLabel extends Statement {

	/**
	 * The set of implemented labels
	 **/
	private Vector labels;

	/*@
	  @ private invariant labels != null;
	  @ private invariant labels.elementType <: \type(Expression)
	  @*/

	/**
	 * Constructs a statement as a <i>parsed item</i>.
	 * @param jf The file where the statement is located
	 * @param tree The <code>AST</code> node corresponding to the statement
	 * @see jml2b.structure.java.ParsedItem#ParsedItem(JmlFile, AST)
	 **/
	protected StImplementsLabel(JmlFile jf, AST tree) {
		super(jf, tree);
		labels = new Vector();
	}

	public String emit() {
		boolean b = false;
		String s = "/*@ implements ";
		Enumeration e = labels.elements();
		while (e.hasMoreElements()) {
			Expression element = (Expression) e.nextElement();
			if (b)
				s += ",";
			else
				b = true;
			s += element.emit();
		}
		return s;
	}

	/**
	 * Parses an <code>AST</code> tree in order to complete the label set.
	 * @param tree <code>AST</code> tree containing the the label list
	 * @throws Jml2bException when a parse error occurs.
	 **/
	private void parseLabel(AST tree) throws Jml2bException {
		switch (tree.getType()) {
			case COMMA :
				parseLabel(tree.getFirstChild());
				parseLabel(tree.getFirstChild().getNextSibling());
				break;
			case IDENT :
				Expression e = Expression.createE(getJmlFile(), tree);
				e.parse(tree);
				labels.add(e);
				break;
		}
	}

	public AST parse(AST tree) throws Jml2bException {
		parseLabel(tree.getFirstChild());
		//@ set parsed = true;
		return tree.getNextSibling();
	}

	public LinkInfo linkStatement(IJml2bConfiguration config, LinkContext f) {
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
	 * Selects in the lemmas corresponding to normal behaviour, the cases 
	 * corresponding to the set of implemented labels.
	 * @throws PogException when a wrong label is detected
	 **/
	public Proofs wp(
		IJml2bConfiguration config,
		Proofs normalBehaviour,
		Proofs finishOnReturn,
		LabeledProofsVector finishOnBreakLab,
		LabeledProofsVector finishOnContinueLab,
		ExceptionalBehaviourStack exceptionalBehaviour)
		throws PogException {
		try {
			return ((Proofs) normalBehaviour.clone()).selectLabel(labels);
		} catch (WrongLabelException wle) {
			throw new PogException("Wrong label", this);
		}
	}

	static final long serialVersionUID = 5276356605510345886L;

	public void getPrecondition(
		IJml2bConfiguration config,
		ModifiableSet modifies,
		Vector req,
		Vector ens) {
	}
	

	public void getAssert(Vector asser) {
	}

	public void getSpecBlock(Vector asser) {
	}

	public void getLoop(Vector asser) {
	}

	public void collectCalledMethod(Vector calledMethod) {}

}
