//******************************************************************************
/* Copyright (c) 2005 INRIA. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: CoqException.java
/*
/********************************************************************************
/* Warnings/Remarks:
/*******************************************************************************/
package prover.exec.exceptions;

import prover.exec.AProverException;

/**
 * @author J. Charles
 */
public class ProverException extends AProverException {
	/**
	 * 
	 */
	private static final long serialVersionUID = 1L;

	public ProverException(String description) {
		super(description);
	}
	
	public ProverException(String location, String description) {
		super("ProverEditor." + location + ": " + description);
	}
}
