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

import jml.JmlDeclParserTokenTypes;
import jml2b.IJml2bConfiguration;
import jml2b.exceptions.Jml2bException;
import jml2b.link.LinkContext;
import jml2b.pog.util.IdentifierResolver;
import jml2b.structure.java.Field;
import jml2b.structure.java.JmlFile;
import jml2b.structure.java.ParsedItem;
import jml2b.structure.java.Type;
import antlr.collections.AST;

/**
 * This class implements a list of quantified fields.
 * @author L. Burdy, A. Requet
 **/
public class QuantifiedVar extends ParsedItem {

	/**
	 * The current quantified field
	 **/
	/*@ non_null */
	private Field field;

	/**
	 * The next element of the list
	 **/
	private QuantifiedVar next;

	/**
	 * Constructs an expression as a <i>parsed item</i>.
	 * @param jf The file where the statement is located
	 * @param tree The <code>AST</code> node corresponding to the statement
	 * @see jml2b.structure.java.ParsedItem#ParsedItem(JmlFile, AST)
	 **/
	QuantifiedVar(JmlFile jf, AST tree) throws Jml2bException {
		super(jf, tree);
		Type type = new Type(getJmlFile(), tree.getFirstChild());
		type.parse(tree.getFirstChild());
		AST tree1 = tree.getFirstChild().getNextSibling();
		if (tree1.getType() == JmlDeclParserTokenTypes.COMMA) {
			field =
				new Field(
					new ParsedItem(getJmlFile(), tree1.getFirstChild().getNextSibling()),
					type,
					tree1.getFirstChild().getNextSibling().getText());
			next = new QuantifiedVar(jf, type, tree1.getFirstChild());
		} else
			field =
				new Field(
					new ParsedItem(getJmlFile(), tree1),
					type,
					tree1.getText());

		if (tree.getNextSibling() != null) {
			add(new QuantifiedVar(jf, tree));
		}
	}

	public QuantifiedVar(JmlFile jf, Type type, AST ast) {
		if (ast.getType() == JmlDeclParserTokenTypes.COMMA) {
			field =
				new Field(
					new ParsedItem(getJmlFile(), ast.getFirstChild().getNextSibling()),
					type,
					ast.getFirstChild().getNextSibling().getText());
			next = new QuantifiedVar(jf, type, ast.getFirstChild());
		} else
			field =
				new Field(
					new ParsedItem(getJmlFile(), ast),
					type,
					ast.getText());
	}

	private void add(QuantifiedVar var) {
		if (next == null)
			next = var;
		else
			next.add(var);
	}

	/**
	 * Constructs a quantified fields list form another one.
	 * @param pi The parsed item corresponding to the list
	 * @param f The current field
	 * @param n The tail of the list
	 **/
	/*@
	  @ requires f != null;
	  @*/
	public QuantifiedVar(ParsedItem pi, Field f, QuantifiedVar n) {
		super(pi);
		field = f;
		next = n;
	}

	/**
	 * Clones the list of quantified fields
	 * @return the cloned list
	 **/
	public Object clone() {
		return new QuantifiedVar(
			this,
			field,
			next == null ? null : (QuantifiedVar) next.clone());
	}

	/**
	 * Returns whether two lists are equal.
	 * @param q The tested list
	 * @return <code>true</code> if the list equals the parameter, 
	 * <code>false</code> otherwise
	 **/
	public boolean equals(QuantifiedVar q) {
		return field == q.field
			&& (next == null
				? q.next == null
				: (q.next != null && next.equals(q.next)));
	}

	/**
	 * Displays the expression corresponding to a part of a method specification
	 * in a tool tip with the initial Java syntax.
	 * @return the string corresponding to this list
	 **/
	String toJava() {
		return field.getType().toJava()
			+ " "
			+ field.getName()
			+ (next == null ? "" : "," + next.toJava());
	}

	void linkStatement(IJml2bConfiguration config, LinkContext f)
		throws Jml2bException {
		field.link(config, f);
		f.linkVars.add(field);
		if (next != null)
			next.linkStatement(config, f);
	}

	/**
	 * Give an index in the identifer array to the fields of the list
	 * @see jml2b.pog.IdentifierResolver#bIdents
	 **/
	void processIdent() {
		field.nameIndex = IdentifierResolver.addIdent(field);
		if (next != null)
			next.processIdent();
	}

	/**
	 * Returns the set of parsed items that correspond to this expression
	 * @return the set of parsed item that correspond to the complete 
	 * expression 
	 **/
	public Vector getParsedItems() {
		Vector res = new Vector();
		res.add((ParsedItem) field);
		if (next != null)
			res.addAll(next.getParsedItems());
		return res;
	}

	public void setParsedItem(ParsedItem pi) {
		field.setParsedItem(pi);
		if (next != null)
			next.setParsedItem(pi);
	}

	/**
	 * Returns the current field.
	 * @return <code>field</code>
	 */
	public Field getField() {
		return field;
	}

	/**
	 * Returns the next element of the list.
	 * @return <code>next</code>
	 */
	public QuantifiedVar getNext() {
		return next;
	}

	static final long serialVersionUID = -7810447303875024252L;

}
