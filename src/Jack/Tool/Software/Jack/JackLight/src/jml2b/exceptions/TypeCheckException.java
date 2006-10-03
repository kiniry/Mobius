//******************************************************************************
/* Copyright (c) 2003 INRIA. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: 
/*
/*******************************************************************************
/* Warnings/Remarks:
/******************************************************************************/
package jml2b.exceptions;

import jml2b.structure.java.ParsedItem;

/**
 * @author lburdy
 *
 * To change the template for this generated type comment go to
 * Window&gt;Preferences&gt;Java&gt;Code Generation&gt;Code and Comments
 */
public class TypeCheckException extends Jml2bException {
	/**
	 * 
	 */
	private static final long serialVersionUID = 1L;
	private int line;
	private int column;
	private String errorMessage;

	//@ requires b != null;
	public TypeCheckException(String message, ParsedItem b) {
		// add and fix the line number.
		super("Line " + (b.getLine() + 1) + ": " + message);
		line = b.getLine() + 1;
		column = b.getColumn();
		errorMessage = message;
	}

	public int getLine() {
		return line;
	}

	public int getColumn() {
		return column;
	}

	public String getMessage() {
		return errorMessage;
	}
}
