//******************************************************************************
/* Copyright (c) 2002, 2003 GEMPLUS Software Research Labs. All Rights Reserved.
/* Copyright (c) 2003, 2004 INRIA. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: TTypeExp.java
/*
/*******************************************************************************
/* Warnings/Remarks:
/******************************************************************************/
package jml2b.structure.statement;

import java.util.Set;
import java.util.Vector;

import jml2b.IJml2bConfiguration;
import jml2b.exceptions.Jml2bException;
import jml2b.formula.IFormToken;
import jml2b.formula.TTypeForm;
import jml2b.link.LinkContext;
import jml2b.link.LinkInfo;
import jml2b.pog.lemma.FormulaWithPureMethodDecl;
import jml2b.structure.java.Field;
import jml2b.structure.java.JmlFile;
import jml2b.structure.java.Modifiers;
import jml2b.structure.java.ParsedItem;
import jml2b.structure.java.Type;
import jml2b.structure.jml.JmlExpression;
import jml2b.util.ModifiableSet;
import antlr.collections.AST;

/**
 * This class implements expressions corresponding to types.
 * @author L. Burdy, A. Requet
 **/
public class TTypeExp extends Expression {
	/**
	 * The type encapsulated in this expression
	 **/
	private Type type;

	/*@
	  @ invariant parsed ==> type != null;
	  @*/

	/**
	 * Constructs an expression as a <i>parsed item</i>.
	 * @param jf The file where the statement is located
	 * @param tree The <code>AST</code> node corresponding to the statement
	 * @see jml2b.structure.java.ParsedItem#ParsedItem(JmlFile, AST)
	 **/
	TTypeExp(JmlFile jf, AST tree) {
		super(jf, tree);
	}

	/*@
	  @ requires t != null;
	  @*/
	public TTypeExp(Type t) {
		//@ set parsed = true;
		type = t;
	}

	public Object clone() {
		return this;
	}

	public boolean equals(Expression e) {
		return getNodeType() == e.getNodeType()
			&& type.equals(((TTypeExp) e).type);
	}

	FormulaWithPureMethodDecl exprToContextForm(
		IJml2bConfiguration config,
		Vector methods,
		boolean pred) {
		TTypeForm res = new TTypeForm(IFormToken.Jm_T_TYPE, type);
		return new FormulaWithPureMethodDecl(res);
	}

	public String toJava(int indent) {
		return type.toJava();
	}

	/*@
	  @ modifies type;
	  @ ensures type != null;
	  @*/
	public AST parse(AST tree) throws Jml2bException {
		//@ set parsed = true;
		setNodeType(tree.getType());
		setNodeText(tree.getText());
		type = new Type(getJmlFile(), tree.getFirstChild());
		type.parse(tree.getFirstChild());
		return tree.getNextSibling();
	}

	public LinkInfo linkStatement(IJml2bConfiguration config, LinkContext f)
		throws Jml2bException {
		type.link(config, f);
		setStateType(Type.getType());
		return new LinkInfo(getStateType());
	}

	public Type typeCheck(IJml2bConfiguration config, LinkContext f)
		throws Jml2bException {
		return Type.getType();
	}

	public void processIdent() {
	}

	public void isModifiersCompatible(IJml2bConfiguration config, Modifiers modifiers) {
	}

	public JmlExpression instancie() {
		return this;
	}

	public Expression subField(Field f, Field newF) {
		return this;
	}

	public Expression subResult(String ww) {
		return this;
	}

	public JmlExpression instancie(Expression b) {
		return this;
	}

	public boolean isConstant() {
		return false;
	}

	public Vector getParsedItems() {
		Vector res = new Vector();
		res.add((ParsedItem) type);
		return res;
	}

	public void setParsedItem(ParsedItem pi) {
		type.setParsedItem(pi);
	}

	//  Vector getFreshVars() {
	//      return new Vector();
	//  }

	public void old() {
	}

	public void getPrecondition(
		IJml2bConfiguration config,
		ModifiableSet modifies,
		Vector req,
		Vector ens) {
	}

	public void collectCalledMethod(Vector calledMethod) {

	}
		static final long serialVersionUID = -7191104311045926981L;

	void getFreeVariable(Set s) {
	}

}
