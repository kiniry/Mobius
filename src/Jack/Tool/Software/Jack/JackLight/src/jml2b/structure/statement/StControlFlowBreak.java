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
import jml2b.link.LinkContext;
import jml2b.link.LinkInfo;
import jml2b.structure.java.Class;
import jml2b.structure.java.JmlFile;
import jml2b.structure.java.Type;
import antlr.collections.AST;

/**
* This class implements a control flow break statement, that is a 
* <code>throw</code>, a <code>continue</code>, a <code>break</code> or a
* <code>return</code>.
* @author L. Burdy
**/
public class StControlFlowBreak extends Statement {

	/**
	 * The node type can be <code>LITERAL_return</code>, 
	 * <code>LITERAL_break</code>, <code>LITERAL_continue</code>,
	 * <code>LITERAL_throw</code>.
	 **/
	private int nodeType;

	/**
	 * The expression of this statement. It can be the expression returned, the
	 * expression thrown or the label for a <code>break</code> or a 
	 * <code>continue</code>. It can be null except for a <code>throw</code>.
	 **/
	private Expression exp;

	/**
	 * Construct an empty statement that will be filled during the parse
	 * @param jf The JML file
	 * @param tree The current AST tree node
	 **/
	protected StControlFlowBreak(JmlFile jf, AST tree) {
		super(jf, tree);
	}

	public String emit() {
		String s = "";
		switch (nodeType) {
			case LITERAL_throw :
				s += "throw ";
				break;
			case LITERAL_return :
				s += "return ";
				break;
			case LITERAL_break :
				s += "break ";
				break;
			case LITERAL_continue :
				s += "continue ";
				break;
		}
		if (exp != null)
			s += exp.toJava(0);
		s += ";\n";
		return s;
	}

	public AST parse(AST tree) throws Jml2bException {
		nodeType = tree.getType();
		if (tree.getFirstChild() != null) {
			exp = Expression.createE(getJmlFile(), tree.getFirstChild());
			exp.parse(tree.getFirstChild());
		}
		return tree.getNextSibling();
	}

	public LinkInfo linkStatement(IJml2bConfiguration config, LinkContext f)
		throws Jml2bException {
		if (nodeType != LITERAL_break
			&& nodeType != LITERAL_continue
			&& exp != null)
			return exp.linkStatement(config, f);
		else
			return null;
	}

	public Type typeCheck(IJml2bConfiguration config, LinkContext f)
		throws Jml2bException {
		return null;
	}

	public Statement jmlNormalize(
		IJml2bConfiguration config,
		Class definingClass) {
		if (exp != null)
			exp = (Expression) exp.jmlNormalize(config, definingClass);
		return this;
	}

	static final long serialVersionUID = -193895196844984447L;

	public void collectCalledMethod(Vector calledMethod) {
		if (exp != null)
			exp.collectCalledMethod(calledMethod);
	}

	public void getAssert(Vector asser) {
	}
	
	public void getSpecBlock(Vector asser) {
	}
	public void getLoop(Vector asser) {
	}
}