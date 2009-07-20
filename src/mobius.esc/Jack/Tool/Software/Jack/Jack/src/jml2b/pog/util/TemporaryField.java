//******************************************************************************
/* Copyright (c) 2002, 2003 GEMPLUS Software Research Labs. All Rights Reserved.
/* Copyright (c) 2003 INRIA. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: TemporaryField
/*
/*******************************************************************************
/* Warnings/Remarks:
/******************************************************************************/
package jml2b.pog.util;

import jml2b.structure.java.Field;
import jml2b.structure.java.IModifiers;
import jml2b.structure.java.Modifiers;
import jml2b.structure.java.ParsedItem;
import jml2b.structure.java.Type;
import jml2b.structure.statement.Expression;

/**
 * This class provides services to create and use temporary fields that are 
 * usefull during the proof obligation calculation.
 * @author L. Burdy
 */
public class TemporaryField extends Field {

	/**
	 * Constructs a temporary field from a field with a new name.
	 * @param pi The parsed item associated to the field
	 * @param m The modifiers associated with the field
	 * @param t The type of the field
	 * @param n The new name
	 * @param a The initialization associated with this field
	 **/
	public TemporaryField(
		ParsedItem pi,
		IModifiers m,
		Type t,
		String n,
		Expression a) {
		super(pi, m, t, n, a);
	}

	/**
	 * Constructs a tempory field with a given name and a given type.
	 * @param pi The parsed item associated to the field
	 * @param t The type of the field
	 * @param n The name of the field
	 **/
	public TemporaryField(ParsedItem pi, Type t, String n) {
		super(pi, t, n);
	}

	/**
	 * Returns the name of the field.
	 * @return The name of the field
	 **/
	public String getBName() {
		return getName();
	}

	static final long serialVersionUID = -9198845858103042990L;
}
