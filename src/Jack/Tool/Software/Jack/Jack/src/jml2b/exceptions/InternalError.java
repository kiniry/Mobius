///******************************************************************************
//* Copyright (c) 2002, 2003 GEMPLUS Software Research Labs. All Rights Reserved.
//*------------------------------------------------------------------------------
//* Name: InternalError.java
//*
//********************************************************************************
//* Warnings/Remarks:
//*******************************************************************************/
package jml2b.exceptions;

/**
 * Exception class used to report internal errors in Jack.
 * 
 * It can be used either to indicate bugs (cases that should are not expected
 * to happen) or either to indicate installation or configuration problem, 
 * for instance when the class <code>java.lang.Object</code> cannot be 
 * loaded.
 * 
 * @author A. Requet
 */
public class InternalError extends Error {
	/**
	 * 
	 */
	private static final long serialVersionUID = 1L;

	public InternalError(String s) {
		super(s);
	}
}
