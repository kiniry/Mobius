//******************************************************************************
/* Copyright (c) 2002, 2003 GEMPLUS Software Research Labs. All Rights Reserved.
/* Copyright (c) 2003, 2004 INRIA. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: SpecArrayDotDot.java
/*
/*******************************************************************************
/* Warnings/Remarks:
/******************************************************************************/
package jml2b.structure.jml;

import java.util.Vector;

import jml2b.IJml2bConfiguration;
import jml2b.exceptions.Jml2bException;
import jml2b.exceptions.PogException;
import jml2b.formula.BinaryForm;
import jml2b.link.LinkContext;
import jml2b.link.LinkInfo;
import jml2b.pog.lemma.FormulaWithPureMethodDecl;
import jml2b.structure.java.Field;
import jml2b.structure.java.JmlFile;
import jml2b.structure.java.ParsedItem;
import jml2b.structure.java.Type;
import jml2b.structure.statement.Expression;
import antlr.collections.AST;

/**
 * This class represents an indexes interval
 * @author L. Burdy
 **/
public class SpecArrayDotDot extends SpecArray {

	/**
	 * The low boundary mark as an expression
	 **/
	private Expression e1;

	/**
	 * The high boudary mark as an expression
	 **/
	private Expression e2;

	/**
	 * The low boundary mark as a formula
	 **/
	private transient FormulaWithPureMethodDecl f1;

	/**
	 * The high boundary mark as a formula
	 **/
	private transient FormulaWithPureMethodDecl f2;

	/**
	 * Constructs an empty interval corresponding to a parsed item.
	 * @param jf The current JML file
	 * @param tree The tree corresponding to this modifies
	 **/
	SpecArrayDotDot(JmlFile jf, AST tree) throws Jml2bException {
		super(jf, tree);
		e1 = Expression.createE(jf, tree.getFirstChild());
		e1.parse(tree.getFirstChild());
		e2 = Expression.createE(jf, tree.getFirstChild().getNextSibling());
		e2.parse(tree.getFirstChild().getNextSibling());
	}

	/**
	 * Constructs an interval corresponding to a formula.
	 * @param pi The parsed item
	 * @param f The formula
	 **/
	SpecArrayDotDot(ParsedItem pi, FormulaWithPureMethodDecl f1, FormulaWithPureMethodDecl f2) {
		super(pi);
		this.f1 = f1;
		this.f2 = f2;
	}

	/**
	 * Constructs an interval from another one.
	 * @param pi The parsed item
	 * @param e1 The low boundary mark
	 * @param e2 The high boundary mark
	 **/
	private SpecArrayDotDot(ParsedItem pi, Expression e1, Expression e2) {
		super(pi);
		this.e1 = e1;
		this.e2 = e2;
	}

	public Object clone() {
		if(e1 != null) {
			return new SpecArrayDotDot(
					this,
					(Expression) e1.clone(),
					(Expression) e2.clone());
		}
		else {
			return new SpecArrayDotDot(
					this,
					(FormulaWithPureMethodDecl) f1.clone(),
					(FormulaWithPureMethodDecl) f2.clone());
		}
	}

	Vector getParsedItems() {
		Vector res = e1.getParsedItems();
		res.addAll(e2.getParsedItems());
		return res;
	}

	void setParsedItem(ParsedItem pi) {
		e1.setParsedItem(pi);
		e2.setParsedItem(pi);
	}

	/**
	 * @throws InternalError since this represents a set of modified indexes
	 */
	FormulaWithPureMethodDecl getFormula(IJml2bConfiguration config) {
		throw new InternalError("SpecArrayDotDot.getFormula");
	}

	/**
	 * @return <code>e1 .. e2</code>
	 **/
	FormulaWithPureMethodDecl getSet(IJml2bConfiguration config, Modifies m)
		throws PogException {
		FormulaWithPureMethodDecl fwp1 = getF1(config);
			FormulaWithPureMethodDecl fwp2 = getF2(config);
			
		return new FormulaWithPureMethodDecl(fwp1, fwp2, new BinaryForm(B_INTERVAL, fwp1.getFormula(), fwp2.getFormula()));
	}

	/**
	 * @return <code>e1 .. e2</code>
	 **/
	String toJava(int indent) {
		return e1.toJava(indent) + ".." + e2.toJava(indent);
	}

	LinkInfo linkStatement(IJml2bConfiguration config, LinkContext f)
		throws Jml2bException {
		e1.linkStatement(config, f);
		return e2.linkStatement(config, f);
	}

	public Type typeCheck(IJml2bConfiguration config, LinkContext f)
		throws Jml2bException {
		e1.typeCheck(config, f);
		e2.typeCheck(config, f);
		return null;
	}

	SpecArray instancie() {
		e1 = (Expression) e1.instancie();
		e2 = (Expression) e2.instancie();
		return this;
	}

	void instancie(Expression b) {
		e1 = (Expression) e1.instancie(b);
		e2 = (Expression) e2.instancie(b);
	}

	SpecArray sub(IJml2bConfiguration config, Modifies m, Field a, Field b)
		throws PogException {
		return new SpecArrayDotDot(
			this,
			getF1(config).sub(a, b, true),
			getF2(config).sub(a, b, true));
	}

	void processIdent() {
		e1.processIdent();
		e2.processIdent();
	}

	/**
	 * Returns the low boundary mark
	 **/
	FormulaWithPureMethodDecl getF1(IJml2bConfiguration config) throws PogException {
		try {

			if (f1 == null)
				f1 = e1.exprToForm(config);
			return f1;
		} catch (Jml2bException je) {
			throw new jml2b.exceptions.InternalError(je.toString());
		}

	}

	/**
	 * Returns the high boundary mark
	 **/
	FormulaWithPureMethodDecl getF2(IJml2bConfiguration config) throws PogException {
		try {
			if (f2 == null)
				f2 = e2.exprToForm(config);
			return f2;
		} catch (Jml2bException je) {
			throw new jml2b.exceptions.InternalError(je.toString());
		}

	}

	/**
	 * @return
	 */
	public Expression getE1() {
		return e1;
	}

	/**
	 * @return
	 */
	public Expression getE2() {
		return e2;
	}

	public boolean equals(Object obj) {
		return obj instanceof SpecArrayDotDot
			&& getE1().equals(((SpecArrayDotDot) obj).getE1())
			&& getE2().equals(((SpecArrayDotDot) obj).getE2());
	}

	static final long serialVersionUID = -7820036551486276520L;

}
