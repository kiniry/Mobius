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
