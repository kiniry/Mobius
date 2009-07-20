//******************************************************************************
/* Copyright (c) 2002, 2003 GEMPLUS Software Research Labs. All Rights Reserved.
/* Copyright (c) 2003, 2004 INRIA. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: ArrayInitializer.java
/*
/*******************************************************************************
/* Warnings/Remarks:
/*  09/26/2003 : Simplify integration achieved
/******************************************************************************/
package jml2b.structure.statement;

import java.io.Serializable;
import java.util.Set;
import java.util.Vector;

import jml.JmlDeclParserTokenTypes;
import jml2b.IJml2bConfiguration;
import jml2b.exceptions.Jml2bException;
import jml2b.formula.IFormToken;
import jml2b.link.LinkContext;
import jml2b.link.LinkInfo;
import jml2b.pog.lemma.FormulaWithPureMethodDecl;
import jml2b.structure.java.Field;
import jml2b.structure.java.JmlFile;
import jml2b.structure.java.Modifiers;
import jml2b.structure.java.ParsedItem;
import jml2b.structure.java.Type;
import jml2b.structure.jml.JmlExpression;
import jml2b.util.Profiler;
import antlr.collections.AST;

/**
 * This class implements a list of expressions corresponding to an array 
 * initializer.
 * @author L. Burdy, A. Requet
 **/
class ListExp
	extends Profiler
	implements JmlDeclParserTokenTypes, Serializable, IFormToken {

	/**
	 * The current expression
	 **/
	private Expression exp;

	/*@
	  @ private ghost boolean parsed = false;
	  @ invariant parsed ==> exp != null;
	  @ invariant parsed && next != null ==> next.parsed;
	  @*/

	/**
	 * The next element of the list
	 **/
	private ListExp next;

	/**
	 * Clones the list
	 * @return the cloned list
	 **/
	/*@
	  @ requires parsed;
	  @*/
	public Object clone() {
		ListExp res = new ListExp();
		res.exp = (Expression) exp.clone();
		res.next = next == null ? null : (ListExp) next.clone();
		//@ set res.parsed = true;
		return res;
	}

	/**
	 * Returns whether two list are equal.
	 * @param l The tested list
	 * @return <code>true</code> if the list equals the parameter, 
	 * <code>false</code> otherwise
	 **/
	/*@
	  @ requires parsed && l != null && l.parsed;
	  @*/
	public boolean equals(ListExp l) {
		return exp.equals(l.exp)
			&& (next == null
				? l.next == null
				: (l.next != null && next.equals(l.next)));
	}

	/**
	 * Parses an <code>AST</code> tree in order to instanciate the fields.
	 * @param jmlFile The current JML file
	 * @param tree <code>AST</code> tree containing the statement
	 * @return the remaining non parsed tree.
	 * @throws Jml2bException when a parse error occurs.
	 **/
	/*@
	  @ modifies exp, next;
	  @ ensures exp != null && parsed;
	  @*/
	AST parse(JmlFile jmlFile, AST tree) throws Jml2bException {
		exp = Expression.createE(jmlFile, tree);
		AST subtree = exp.parse(tree);
		if (subtree.getType() != RCURLY) {
			next = new ListExp();
			return next.parse(jmlFile, subtree);
		} else
			return subtree.getNextSibling();
		//@ set parsed = true;
	}

	/**
	 * Links the statement.
	 * @return the link info resulting from the link
	 * @throws Jml2bException
	 **/
	/*@
	  @ requires parsed;
	  @*/
	LinkInfo linkStatement(IJml2bConfiguration config, LinkContext f)
		throws Jml2bException {
		exp.linkStatement(config, f);
		if (next != null)
			next.linkStatement(config, f);
		return null;
	}

	/**
	 * Collects all the indentifier of the list to give them an index in the 
	 * identifer array. This array is then analyzed to give short name when it
	 * is possible to identifiers.
	 * @see jml2b.pog.IdentifierResolver#bIdents
	 **/
	/*@
	  @ requires parsed;
	  @*/
	void processIdent() {
		exp.processIdent();
		if (next != null)
			next.processIdent();
	}

	/** 
	 * Replaces <code>this</code> with the parameter in the expressions.
	 * @param b expression on which the method where the expression occurs is 
	 * called.
	 * @return the modified list
	 **/
	/*@
	  @ requires parsed;
	  @*/
	ListExp instancie(Expression b) {
		exp = (Expression) exp.instancie(b);
		next = (next == null ? null : next.instancie(b));
		return this;
	}

	/**
	 * Returns the set of parsed items that correspond to those expressions
	 * @return the set of parsed item that correspond to the expressions 
	 * of the list 
	 **/
	/*@
	  @ requires parsed;
	  @*/
	public Vector getParsedItems() {
		Vector res = exp.getParsedItems();
		if (next != null)
			res.addAll(next.getParsedItems());
		return res;
	}

	public void setParsedItem(ParsedItem pi) {
		exp.setParsedItem(pi);
		if (next != null)
			next.setParsedItem(pi);
	}

		static final long serialVersionUID = 3986804042295473223L;

	/**
	 * @return
	 */
	public Expression getExp() {
		return exp;
	}

	/**
	 * @return
	 */
	public ListExp getNext() {
		return next;
	}

}

/**
 * This class implements an array initializer statement, that is, for instance,  
 * <code>{ {"car", "house" }, {"dog", "cat", "monkey"} }</code>.
 * @author L. Burdy
 **/
public class ArrayInitializer extends Expression {

	/**
	 * The list of expressions. Those expression can be array initializer 
	 * themseleves when a multi-dimensionnal array is parsed. It can be
	 * <code>null</code> if the array has an empty initialization
	 **/
	private ListExp listExp;

	/**
	 * Constructs an expression as a <i>parsed item</i>.
	 * @param jf The file where the statement is located
	 * @param tree The <code>AST</code> node corresponding to the statement
	 * @see jml2b.structure.java.ParsedItem#ParsedItem(JmlFile, AST)
	 **/
	protected ArrayInitializer(JmlFile jf, AST tree) {
		super(jf, tree);
	}

	/**
	 * Constructs an array initializer from another one.
	 * @param l The expression list
	 **/
	private ArrayInitializer(ListExp l) {
		listExp = l;
		//@ set parsed = true;
	}

	/**
	 * Clones the array initializer
	 * @return hte cloned array initializer
	 **/
	public Object clone() {
		ArrayInitializer res =
			new ArrayInitializer(
				listExp == null ? null : (ListExp) listExp.clone());
		res.setBox(this);
		return res;
	}

	public boolean equals(Expression e) {
		return e instanceof ArrayInitializer
			&& listExp == null
				? ((ArrayInitializer) e).listExp == null
				: (((ArrayInitializer) e).listExp != null
					&& listExp.equals(((ArrayInitializer) e).listExp));
	}

	/**
	 * @throws InternalError since an array initializer appears only in 
	 * expression with side effects.
	 **/
	FormulaWithPureMethodDecl exprToContextForm(
		IJml2bConfiguration config,
		Vector methods,
		boolean pred) {
		throw new jml2b.exceptions.InternalError(
			"Unreachable code reached : ArrayInitializer.exprToContextForm");
	}

	public AST parse(AST tree) throws Jml2bException {
		AST subtree = tree.getNextSibling();
		if (subtree.getType() == RCURLY)
			return subtree.getNextSibling();
		listExp = new ListExp();
		//@ set parsed = true;
		return listExp.parse(getJmlFile(), subtree);
	}

	/**
	 * @throws InternalError since an array initializer appears only in 
	 * expression with side effects.
	 **/
	public String toJava(int indent) {
		throw new jml2b.exceptions.InternalError(
			"Unreachable code reached : ArrayInitializer.exprToContextForm");
	}

	public LinkInfo linkStatement(IJml2bConfiguration config, LinkContext f)
		throws Jml2bException {
		if (listExp != null) {
			listExp.linkStatement(config, f);
		}
		return null;
	}

	public Type typeCheck(IJml2bConfiguration config, LinkContext f)
		throws Jml2bException {
		return null;
	}

	public void processIdent() {
		if (listExp != null)
			listExp.processIdent();
	}

	public Expression subField(Field f, Field newF) {
		return this;
	}

	public Expression subResult(String ww) {
		return this;
	}

	/**
	 * @throws InternalError since an array initializer appears only in 
	 * expression with side effects.
	 **/
	public void isModifiersCompatible(IJml2bConfiguration config, Modifiers modifiers) {
		throw new jml2b.exceptions.InternalError(
			"Unreachable code reached : ArrayInitializer.exprToContextForm");
	}

	public JmlExpression instancie(Expression b) {
		if (listExp != null)
			listExp = listExp.instancie(b);
		return this;
	}

	public JmlExpression instancie() {
		return this;
	}

	public boolean isConstant() {
		return false;
	}

	//	Vector getFreshVars() {
	//		return new Vector();
	//	}

	public Vector getParsedItems() {
		Vector res = new Vector();
		if (listExp != null)
			res = listExp.getParsedItems();
		res.add((ParsedItem) this);
		return res;
	}

	public void setParsedItem(ParsedItem pi) {
		if (listExp != null)
			listExp.setParsedItem(pi);
		change(pi);
	}

	/**
	 * @throws InternalError since an array initializer appears only in 
	 * expression with side effects.
	 **/
	public void old() {
		throw new jml2b.exceptions.InternalError(
			"Unreachable code reached : ArrayInitializer.exprToContextForm");
	}

		static final long serialVersionUID = 1890926686273759548L;

	public void collectCalledMethod(Vector calledMethod) {
		ListExp le = listExp;
		while (le != null) {
			le.getExp().collectCalledMethod(calledMethod);
			le = le.getNext();
		}
	}

	void getFreeVariable(Set s) {
	}

}