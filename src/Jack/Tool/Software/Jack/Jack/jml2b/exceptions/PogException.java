///******************************************************************************
//* Copyright (c) 2002, 2003 GEMPLUS Software Research Labs. All Rights Reserved.
//*------------------------------------------------------------------------------
//* Name: PogException.java
//*
//********************************************************************************
//* Warnings/Remarks:
//*******************************************************************************/
package jml2b.exceptions;

import jml2b.structure.java.ParsedItem;

/**
 * This kind of exception is thrown when
 * <UL>
 * <li> a litteral float is found in specification part
 * <li> a loop in pure method called is found in specification part
 * <li> a memory overflow occurs during the WP calculus
 * <li> a class concerning <code>RuntimeException</code> cannot be loaded during
 * the WP calculus.
 * <li> a wrong label is detected
 * </UL>
 * @author L. Burdy
 **/
public class PogException extends Exception {

    /**
	 * 
	 */
	private static final long serialVersionUID = 1L;

	/**
     * Constructs an exception and add an error into the error handler.
     * @param msg message associated to the exception
     * @param b <i>parsed item</i> associated with the exception where the file,
     * the line and the column are taken.
     **/
    //@ requires b != null;
    public PogException(String msg, ParsedItem b) {
        super("Line " + b.getLine() + ": " + msg);
        ErrorHandler.error(b.getJmlFile(), b.getLine(), b.getColumn(), msg);
    }
}
