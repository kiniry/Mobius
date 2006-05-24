//******************************************************************************
//* Copyright (c) 2002, 2003 GEMPLUS Software Research Labs. All Rights Reserved.
/* Copyright (c) 2003, 2004 INRIA. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: Invariant.java
/*
/********************************************************************************
/* Warnings/Remarks:
/*  09/26/2003 : Simplify integration achieved
/*******************************************************************************/
package jml2b.structure.java;

import jml2b.IJml2bConfiguration;
import jml2b.exceptions.Jml2bException;
import jml2b.exceptions.TypeCheckException;
import jml2b.link.LinkContext;
import jml2b.link.TypeCheckable;
import jml2b.structure.statement.Expression;
import antlr.collections.AST;

/** 
 * class representing invariants.
 * 
 * @author A. Requet L. Burdy
 */
public class Invariant extends Declaration implements TypeCheckable {
	/**
	 * Expression corresponding to the invariant.
	 */
	private Expression property;

	/*@
	  @ ghost boolean parsed;
	  @ invariant parsed ==> invariant != null;
	  @*/

	/*@
	  @ requires m != null;
	  @*/
	public Invariant(JmlFile jf, AST tree, Modifiers m, Class defining) {
		super(jf, tree, m, defining);
	}

	Invariant(Expression e, Modifiers m, Class c) {
		super(e, m, c);
		property = e;
	}

	/*@
	  @ requires ast != null;
	  @ requires typeof(ast) <: \type(LineAST);
	  @ modifies invariant;
	  @*/
	public AST parse(JmlFile jmlFile, AST ast) throws Jml2bException {
		//@ set parsed = true;
		property = Expression.createE(jmlFile, ast);
		AST result = property.parse(ast);
		return result;
	}

	/*@
	  @ requires parsed;
	  @*/
	public void link(IJml2bConfiguration config, LinkContext f)
		throws Jml2bException {
		property.link(config, f);
	}

	/*@
	  @ requires parsed;
	  @*/
	public int linkStatements(IJml2bConfiguration config, LinkContext f)
		throws Jml2bException {
		return property.linkStatements(config, f);
		//TODO supprimer temporairement invariant.isModifiersCompatible(modifiers);
	}

	public Type typeCheck(IJml2bConfiguration config, LinkContext f)
		throws Jml2bException {
		Type t = property.typeCheck(config, f);
		if (t.isBoolean())
			return t;
		throw new TypeCheckException(
			"Type mismatch: cannot convert from " + t.toJava() + " to boolean",
			this);
	}

	/**
	 * Returns the name of the invariant.
	 * As invariants do not have names, this implementation always return
	 * null.
	 * 
	 * @return <code>null</code>. 
	 */
	public String getName() {
		return null;
	}

	/**
	 * Returns the expression corresponding to the invariant.
	 * 
	 * @return Expression the invariant.
	 */
	public Expression getInvariant() {
		return property;
	}

	String emit() {
		String s = "/*@ ";
		s += getModifiers().emit();
		s += "invariant\n";
		s += property.toJava(0);
		s += "\n@*/\n";
		return s;
	}

	static final long serialVersionUID = -953617783874540221L;
}
