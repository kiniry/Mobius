///******************************************************************************
//* Copyright (c) 2002, 2003 GEMPLUS Software Research Labs. All Rights Reserved.
//*------------------------------------------------------------------------------
//* Name: ParseException.java
//*
//********************************************************************************
//* Warnings/Remarks:
//*******************************************************************************/
package jml2b.exceptions;

import jml.LineAST;
import jml2b.structure.java.JmlFile;

/**
 * Exception class used to indicate error during the parsing phase.
 * 
 * @author A. Requet
 */
public class ParseException extends Jml2bException {
	/**
	 * 
	 */
	private static final long serialVersionUID = 1L;

	/**
	 * Creates a new ParseException instance.
	 * 
	 * @param f the file that was parsed when the error occured.
	 * @param tree the AST corresponding to the position where the error
	 *         occured.
	 * @param description the description of the error.
	 */
	public ParseException(JmlFile f, LineAST tree, String description) {
		super(description);
		ErrorHandler.error(f, tree.line, tree.column, description);
	}
	
}
