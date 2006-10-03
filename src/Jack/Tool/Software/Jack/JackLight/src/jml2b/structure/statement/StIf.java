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
import jml2b.structure.java.Type;
import antlr.collections.AST;

/**
 * @author lburdy
 *
 * To change the template for this generated type comment go to
 * Window&gt;Preferences&gt;Java&gt;Code Generation&gt;Code and Comments
 */
public /**
* This class implements an <code>if</code> statement.
* @author L. Burdy
**/
class StIf extends Statement {

	/**
	 * The condition
	 **/
	private Expression cond;

	/**
	 * The statement corresponding to the <code>then</code> branch.
	 **/
	private Statement thenTk;

	/**
	 * The statement corresponding to the <code>else</code> branch, if there is 
	 * no <code>else</code> branh, the statement is initialized with 
	 * <code>skip</code>
	 **/
	private Statement elseTk;

	/*@
	  @ invariant parsed ==> cond != null
	  @        && parsed ==> thenTk != null
	  @        && parsed ==> elseTk != null;
	  @*/

	/**
	 * Constructs a statement that will be filled by the parse method.
	 * @param jf The parsed file
	 * @param tree The current tree node
	 **/
	protected StIf(JmlFile jf, AST tree) {
		super(jf, tree);
	}

	/*@
	  @ modifies cond, thenTk, elseTk;
	  @ ensures cond != null && thenTk != null && elseTk != null;
	  @*/
	public AST parse(AST tree) throws Jml2bException {
		cond = Expression.createE(getJmlFile(), tree.getFirstChild());
		AST subtree = cond.parse(tree.getFirstChild());
		thenTk =
			Statement.createS(
				getJmlFile(),
				tree.getFirstChild().getNextSibling());
		subtree = thenTk.parse(tree.getFirstChild().getNextSibling());
		if (subtree != null) {
			elseTk = Statement.createS(getJmlFile(), subtree);
			elseTk.parse(subtree);
		} else {
			elseTk = new StSkip();
		}
		//@ set parsed = true;
		return tree.getNextSibling();
	}

	public LinkInfo linkStatement(IJml2bConfiguration config, LinkContext f)
		throws Jml2bException {
		cond.linkStatement(config, f);
		thenTk.linkStatement(config, f);
		elseTk.linkStatement(config, f);
		return null;
	}

	public Type typeCheck(IJml2bConfiguration config, LinkContext f)
		throws Jml2bException {
		thenTk.typeCheck(config, f);
		elseTk.typeCheck(config, f);
		return null;
	}

	public Statement jmlNormalize(
		IJml2bConfiguration config,
		Class definingClass)
		throws PogException {
		cond = (Expression) cond.jmlNormalize(config, definingClass);
		thenTk = (Statement) thenTk.jmlNormalize(config, definingClass);
		elseTk = (Statement) elseTk.jmlNormalize(config, definingClass);
		return this;
	}

	public void collectCalledMethod(Vector calledMethod) {
		cond.collectCalledMethod(calledMethod);
		thenTk.collectCalledMethod(calledMethod);
		elseTk.collectCalledMethod(calledMethod);
	}


	public void getAssert(Vector asser) {
		thenTk.getAssert(asser);
		elseTk.getAssert(asser);
	}

	public void getSpecBlock(Vector asser) {
		thenTk.getSpecBlock(asser);
		elseTk.getSpecBlock(asser);
	}

	public void getLoop(Vector asser) {
		thenTk.getLoop(asser);
		elseTk.getLoop(asser);
	}

	static final long serialVersionUID = 5726202833367464956L;

}
