///******************************************************************************
//* Copyright (c) 2002, 2003 GEMPLUS Software Research Labs. All Rights Reserved.
//*------------------------------------------------------------------------------
//* Name: TokenException.java
//*
//********************************************************************************
//* Warnings/Remarks:
//*******************************************************************************/
package jml2b.exceptions;

import jml.LineAST;
import jml2b.structure.java.JmlFile;

/**
 * A specialisation of the <code>ParseException</code> class that is used
 * when unexpected tokens are encountered.
 * <p>
 * They usually indicate errors in the Jack parser.
 * 
 * @author A. Requet
 */
public class TokenException extends ParseException {

	/**
	 * 
	 */
	private static final long serialVersionUID = 1L;

	/**
	 * Creates a new <code>TokenException</code> instance.
	 * <p>
	 * Note that the method correspond to the Jack method performing the 
	 * parsing.
	 * 
	 * @param f that contains the unexpected token.
	 * @param tree the AST containing the unexpected token.
	 * @param method the name of the method that throwed the exception.
	 * @param expected the name of the token(s) that was (were) expected.
	 * @param got the name of the token that has been encountered.
	 */
	public TokenException(
		JmlFile f,
		LineAST tree,
		String method,
		String expected,
		String got) {
		super(
			f,
			tree,
			f.fileName.getName()
				+ " : Unexpected token in "
				+ method
				+ ": expected "
				+ expected
				+ ", got "
				+ got);
	}

	/**
	 * Creates a new <code>TokenException</code> instance.
	 * <p>
	 * Note that the method correspond to the Jack method performing the 
	 * parsing.
	 * 
	 * @param f that contains the unexpected token.
	 * @param tree the AST containing the unexpected token.
	 * @param method the name of the method that throwed the exception.
	 * @param expected the name of the token(s) that was (were) expected.
	 * @param got the value of the token that has been encountered.
	 */
	public TokenException(
		JmlFile f,
		LineAST tree,
		String method,
		String expected,
		int got) {
		super(
			f,
			tree,
			f.fileName.getName()
				+ " : Unexpected token in "
				+ method
				+ ": expected "
				+ expected
				+ ", got "
				+ got);
	}

	/**
	 * Creates a new <code>TokenException</code> instance.
	 * <p>
	 * Note that the method correspond to the Jack method performing the 
	 * parsing.
	 * 
	 * @param f that contains the unexpected token.
	 * @param tree the AST containing the unexpected token.
	 * @param method the name of the method that throwed the exception.
	 * @param expected the value of the token that was expected.
	 * @param got the value of the token that has been encountered.
	 */
	public TokenException(
		JmlFile f,
		LineAST tree,
		String method,
		int expected,
		int got) {
		super(
			f,
			tree,
			f.fileName.getName()
				+ " : Unexpected token in "
				+ method
				+ ": expected "
				+ expected
				+ ", got "
				+ got);
	}
}
