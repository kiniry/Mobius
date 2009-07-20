///******************************************************************************
//* Copyright (c) 2002, 2003 GEMPLUS Software Research Labs. All Rights Reserved.
//*------------------------------------------------------------------------------
//* Name: LinkException.java
//*
//********************************************************************************
//* Warnings/Remarks:
//*******************************************************************************/
package jml2b.exceptions;

import jml2b.structure.java.ParsedItem;

/**
 * @author A. Requet
 */
public class LinkException extends Jml2bException {
    /**
	 * 
	 */
	private static final long serialVersionUID = 1L;
	private int line;
    private int column;
    private String errorMessage;

    //@ requires b != null;
    public LinkException(String message, ParsedItem b) {
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
