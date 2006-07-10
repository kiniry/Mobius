//******************************************************************************
/* Copyright (c) 2002, 2003 GEMPLUS Software Research Labs. All Rights Reserved.
/* Copyright (c) 2003, 2004 INRIA. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: SpecArrayStar.java
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
import jml2b.formula.TerminalForm;
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
 * This class describes all the indexes of an array that are declared to be 
 * potentially modified.
 * @author L. Burdy
 **/
public class SpecArrayStar extends SpecArray {

	SpecArrayStar(ParsedItem pi) {
		super(pi);
	}

	/**
	 * Constructs an empty indexes set corresponding to a parsed item.
	 * @param jf The current JML file
	 * @param tree The tree corresponding to this modifies
	 **/
	SpecArrayStar(JmlFile jf, AST tree) {
		super(jf, tree);
	}

	public Object clone() {
		return this;
	}

	Vector getParsedItems() {
		Vector res = new Vector();
		res.add((ParsedItem) this);
		return res;
	}

	void setParsedItem(ParsedItem pi) {
		change(pi);
	}

	/**
	 * @throws InternalError a set of indexes cannot be converted in a formula
	 * that is not a set.
	 **/
	FormulaWithSpecMethodDecl getFormula(IJml2bConfiguration config) {
		throw new InternalError("SpecArrayStar.getFormula()");
	}

	/**
	 * Returns the interval corresponding to the domain of the array.
	 * @return <code>0 .. arraylength(m)-1</code>
	 **/
	FormulaWithSpecMethodDecl getSet(IJml2bConfiguration config, Modifies m)
		throws PogException {
		try {
			FormulaWithSpecMethodDecl fwp = m.getFormula(config);
			return new FormulaWithSpecMethodDecl(fwp, new BinaryForm(
				B_INTERVAL,
				new TerminalForm(0),
				new BinaryForm(
					Ja_NEGATIVE_OP,
					new BinaryForm(
						B_APPLICATION,
						TerminalForm.getArraylength(config),
						fwp.getFormula()),
					new TerminalForm(1))));
		} catch (Jml2bException je) {
			throw new PogException(je.getMessage(), this);
		}
	}

	/**
	 * @return <code>*</code>
	 **/
	String toJava(int indent) {
		return "*";
	}

	LinkInfo linkStatement(IJml2bConfiguration config, LinkContext f)
		throws Jml2bException {
		return null;
	}

	public Type typeCheck(IJml2bConfiguration config, LinkContext f)
		throws Jml2bException {
		return null;
	}

	SpecArray instancie() {
		return this;
	}

	void instancie(Expression b) {
	}

	SpecArray sub(IJml2bConfiguration config, Modifies m, Field a, Field b) {
		return this;
	}

	void processIdent() {
	}

	static final long serialVersionUID = -3630445878113787712L;

	public boolean equals(Object obj) {
		return obj instanceof SpecArrayStar;
	}

}
