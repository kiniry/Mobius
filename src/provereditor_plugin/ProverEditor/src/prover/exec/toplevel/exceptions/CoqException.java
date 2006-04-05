//******************************************************************************
/* Copyright (c) 2005 INRIA. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: CoqException.java
/*
/********************************************************************************
/* Warnings/Remarks:
/*******************************************************************************/
package prover.exec.toplevel.exceptions;

import prover.exec.AProverException;

/**
 * @author J. Charles
 */
public class CoqException extends AProverException {
	/**
	 * 
	 */
	private static final long serialVersionUID = 1L;

	public CoqException(String description) {
		super(description);
	}
}
