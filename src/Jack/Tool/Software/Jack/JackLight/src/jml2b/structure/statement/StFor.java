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
import jml2b.link.LinkContext;
import jml2b.link.LinkInfo;
import jml2b.structure.java.Class;
import jml2b.structure.java.JmlFile;
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
