//******************************************************************************
/* Copyright (c) 2002, 2003 GEMPLUS Software Research Labs. All Rights Reserved.
/* Copyright (c) 2003, 2004 INRIA. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: SpecArrayExpr
/*
/*******************************************************************************
/* Warnings/Remarks:
/******************************************************************************/
package jml2b.structure.jml;

import java.util.Vector;

import jml2b.IJml2bConfiguration;
import jml2b.exceptions.Jml2bException;
import jml2b.exceptions.PogException;
import jml2b.formula.UnaryForm;
import jml2b.link.LinkContext;
import jml2b.link.LinkInfo;
import jml2b.pog.lemma.FormulaWithSpecMethodDecl;
import jml2b.structure.java.Field;
import jml2b.structure.java.JmlFile;
import jml2b.structure.java.ParsedItem;
import jml2b.structure.java.Type;
import jml2b.structure.statement.Expression;
import antlr.collections.AST;

/**
 * This class represents an index of an array
 * @author L. Burdy
 **/
public class SpecArrayExpr extends SpecArray {

	/** 
	 * The expression corresponding to the index
	 **/
	private Expression e;

	/**
	 * The formula corresponding to the index
	 **/
	private transient FormulaWithSpecMethodDecl f;

	/**
	 * Constructs an empty index corresponding to a parsed item.
	 * @param jf The current JML file
	 * @param tree The tree corresponding to this modifies
	 **/
	SpecArrayExpr(JmlFile jf, AST tree) throws Jml2bException {
		super(jf, tree);
		e = Expression.createE(jf, tree);
		e.parse(tree);
	}

	/**
	 * Constructs an index corresponding to a formula.
	 * @param pi The parsed item
	 * @param f The formula
	 **/
	SpecArrayExpr(ParsedItem pi, FormulaWithSpecMethodDecl f) {
		super(pi);
		this.f = f;
	}

	/**
	 * Constructs an index from another one.
	 * @param pi The parsed item
	 * @param e The expression
	 * @param f The formula
	 **/
	private SpecArrayExpr(ParsedItem pi, Expression e, FormulaWithSpecMethodDecl f) {
		super(pi);
		this.e = e;
		this.f = f;
	}

	public Object clone() {
		return new SpecArrayExpr(
			this,
			e == null ? null : (Expression) e.clone(),
			f == null ? null : (FormulaWithSpecMethodDecl) f.clone());
	}

	Vector getParsedItems() {
		return e.getParsedItems();
	}

	void setParsedItem(ParsedItem pi) {
		e.setParsedItem(pi);
	}

	/**
	 * @return <code>f</code>
	 **/
	FormulaWithSpecMethodDecl getFormula(IJml2bConfiguration config) throws PogException {
		try {
			if (f == null)
				return f = e.exprToForm(config);
			else
				return f;
		} catch (Jml2bException je) {
			throw new jml2b.exceptions.InternalError(je.toString());
		}
	}

	/**
	 * @return <code>{f}</code>
	 **/
	FormulaWithSpecMethodDecl getSet(IJml2bConfiguration config, Modifies m)
		throws PogException {
		FormulaWithSpecMethodDecl fwp = getFormula(config);
		return new FormulaWithSpecMethodDecl(fwp, new UnaryForm(B_ACCOLADE, fwp.getFormula()));
	}

	/**
	 * @return <code>e</code>
	 **/
	String toJava(int indent) {
		return e.toJava(indent);
	}

	LinkInfo linkStatement(IJml2bConfiguration config, LinkContext f)
		throws Jml2bException {
		return e.linkStatement(config, f);
	}

	public Type typeCheck(IJml2bConfiguration config, LinkContext f)
		throws Jml2bException {
		e.typeCheck(config, f);
		return null;
	}

	SpecArray instancie() {
		e = (Expression) e.instancie();
		return this;
	}

	void instancie(Expression b) {
		e = (Expression) e.instancie(b);
	}

	SpecArray sub(IJml2bConfiguration config, Modifies m, Field a, Field b)
		throws PogException {
		return new SpecArrayExpr(this, getFormula(config).sub(a, b, true));
	}

	void processIdent() {
		e.processIdent();
	}

	public Expression getE() {
		return e;
	}

	public boolean equals(Object obj) {
		return obj instanceof SpecArrayExpr
			&& getE().equals(((SpecArrayExpr) obj).getE());
	}

	static final long serialVersionUID = -569168750574283801L;

}
