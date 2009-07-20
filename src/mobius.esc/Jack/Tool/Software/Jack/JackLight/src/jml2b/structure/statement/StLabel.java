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
import jml2b.formula.IFormToken;
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
* This class implements a labeled statement
* @author L. Burdy
**/
class StLabel extends Statement implements IFormToken {

	/**
	 * The label
	 **/
	private Expression label;

	/**
	 * The labeled statement
	 **/
	private Statement body;

	/*@
	  @ invariant parsed ==> label != null
	  @        && parsed ==> body != null;
	  @*/

	/**
	 * Constructs a statement that will be filled by the parse method.
	 * @param jf The parsed file
	 * @param tree The current tree node
	 **/
	protected StLabel(JmlFile jf, AST tree) {
		super(jf, tree);
	}

	/*@
	  @ modifies label, body;
	  @ ensures label != null && body != null;
	  @*/
	public AST parse(AST tree) throws Jml2bException {
		label = Expression.createE(getJmlFile(), tree.getFirstChild());
		AST subtree = label.parse(tree.getFirstChild());
		body = Statement.createS(getJmlFile(), subtree);
		subtree = body.parse(subtree);
		//@ set parsed = true;
		return tree.getNextSibling();
	}

	public LinkInfo linkStatement(IJml2bConfiguration config, LinkContext f)
		throws Jml2bException {
		return body.linkStatement(config, f);
	}

	public Type typeCheck(IJml2bConfiguration config, LinkContext f)
		throws Jml2bException {
		return body.typeCheck(config, f);
	}

	public Statement jmlNormalize(
		IJml2bConfiguration config,
		Class definingClass)
		throws PogException {
		body = (Statement) body.jmlNormalize(config, definingClass);
		return this;
	}

		static final long serialVersionUID = -4097123075430569195L;

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
