//******************************************************************************
/* Copyright (c) 2004 INRIA. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: Class.java
/*
/*******************************************************************************
/* Warnings/Remarks:
/******************************************************************************/
package jml2b.structure.java;

import antlr.collections.AST;

/**
 *
 *  @author L. Burdy
 **/
public class Constraint extends Invariant {

	/**
	 * 
	 */
	private static final long serialVersionUID = 1L;

	/*@
	  @ requires m != null;
	  @*/
	public Constraint(JmlFile jf, AST tree, Modifiers m, Class defining) {
		super(jf, tree, m, defining);
	}

	String emit() {
		String s = "/*@ ";
		s += getModifiers().emit();
		s += "constraint\n";
		s += getInvariant().toJava(0);
		s += "\n@*/\n";
		return s;
	}


}
