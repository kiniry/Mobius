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
import jml2b.formula.IModifiesField;
import jml2b.link.LinkContext;
import jml2b.link.LinkInfo;
import jml2b.structure.java.Class;
import jml2b.structure.java.JmlFile;
import jml2b.structure.java.Type;
import jml2b.structure.jml.SpecCase;
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

	public String getNameForModifies() {
		return "after specified block at line " + startLine;
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
