//******************************************************************************
/* Copyright (c) 2002, 2003 GEMPLUS Software Research Labs. All Rights Reserved.
/* Copyright (c) 2003, 2004 INRIA. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: ModifiesNothing
/*
/*******************************************************************************
/* Warnings/Remarks:
/*  09/26/2003 : Simplify integration achieved
/******************************************************************************/
package jml2b.structure.jml;

import java.util.Vector;

import jml2b.IJml2bConfiguration;
import jml2b.exceptions.Jml2bException;
import jml2b.link.LinkContext;
import jml2b.link.LinkInfo;
import jml2b.structure.java.Class;
import jml2b.structure.java.JmlFile;
import jml2b.structure.java.Parameters;
import jml2b.structure.java.ParsedItem;
import jml2b.structure.java.Type;
import jml2b.structure.statement.Expression;
import antlr.collections.AST;

/**
 * This class implements a <code>\nothing</code> modifies clause.
 * @author L. Burdy
 **/
public class ModifiesNothing extends ModifiesClause {

	/**
	 * Constructs a <code>\nothing</code> modifies clause corresponding to a 
	 * parsed item.
	 * @param jf The current JML file
	 * @param a The tree corresponding to this modifies
	 **/
	ModifiesNothing(JmlFile jf, AST a) throws Jml2bException {
		super(jf, a);
	}

	/**
	 * Constructs a <code>\nothing</code> modifies clause
	 */
	public ModifiesNothing() {
	}

	public Object clone() {
		return this;
	}

	public void instancie(IJml2bConfiguration config) {
	}

	public void instancie(Expression b, IJml2bConfiguration config) {
	}

	public LinkInfo linkStatements(IJml2bConfiguration config, LinkContext f)
		throws Jml2bException {
		return null;
	}

	public Type typeCheck(IJml2bConfiguration config, LinkContext f)
		throws Jml2bException {
		return null;
	}

	public void processIdent() {
	}

	/**
	 * @return <code>\nothing</code>
	 **/
	public String toJava(int indent) {
		return "\\nothing";
	}

	/**
	 * @return <code>this</code>
	 */
	public ModifiesClause renameParam(
		IJml2bConfiguration config,
		Parameters signature,
		Vector newSignature) {
		return this;
	}

	/**
	 * Performs no action
	 **/
	public void addDepends(IJml2bConfiguration config, Class c) {
	}

	/**
	 * @return <code>l</code>
	 **/
	public ModifiesClause completeModifiesWithFields(ModifiesList l) {
		return l;
	}

	public void setParsedItem(ParsedItem pi) {
		change(pi);
	}

	static final long serialVersionUID = -2573792837984300742L;

}
