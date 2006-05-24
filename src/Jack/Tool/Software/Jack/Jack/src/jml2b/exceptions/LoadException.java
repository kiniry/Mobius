///******************************************************************************
//* Copyright (c) 2002, 2003 GEMPLUS Software Research Labs. All Rights Reserved.
//*------------------------------------------------------------------------------
//* Name: LoadException.java
//*
//********************************************************************************
//* Warnings/Remarks:
//*******************************************************************************/
package jml2b.exceptions;

/**
 * This class provides an exception that can be threw during the load of a JPO 
 * file. The reasons can be:
 * <UL>
 * <li> the token of a formula is not valid
 * <li> the token of a substitution is not valid
 * <li> the index of an hypothesis is not valid
 * <li> the version of the file is not valid
 * </UL>
 * @author L. Burdy
 * @see jml2b.formula.Formula#create(IJml2bConfiguration, DataInputStream)
 * @see jpov.formula.Formula#create(DataInputStream)
 * @see jml2b.pog.Theorem#findVf(Vector, int)
 * @see jpov.structure.Lemma#findVf(VirtualFormula[], int)
 * @see jml2b.structure.java.JmlFile#loadJmlFile(IJml2bConfiguration, DataInputStream)
 * @see jpov.structure.JmlFile#loadJmlFile(DataInputStream)
 * @see jml2b.structure.java.JmlFile#loadSubstitution(IJml2bConfiguration, DataInputStream)
 * @see jpov.structure.Goal#loadSubstitution(DataInputStream)
 */
public class LoadException extends Exception {
    
    /**
	 * 
	 */
	private static final long serialVersionUID = 1L;

	/**
     * Constructs an exception when a given message.
     * @param msg The message
     **/
	public LoadException(String msg)
	{
		super(msg);
	}
}


