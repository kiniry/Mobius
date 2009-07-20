//******************************************************************************
/* Copyright (c) 2005 INRIA. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: CoqException.java
/*
/********************************************************************************
/* Warnings/Remarks:
/*******************************************************************************/
package mobius.prover.plugins.exceptions;

import mobius.prover.exec.AProverException;


/**
 * A basic implementation of a prover exception.
 * 
 *  @author J. Charles (julien.charles@inria.fr)
 */
public class ProverException extends AProverException {
  /** Serial UID to have much more fun... */
  private static final long serialVersionUID = 1L;

  /**
   * The constructor. Takes a description of the error as parameter.
   * @param description The source of the error.
   */
  public ProverException(final String description) {
    super(description);
  }
  
  /**
   * The constructor. Takes a description of the error and its
   * location as parameters.
   * @param location The location of the error.
   * @param description The source of the error.
   */
  public ProverException(final String location, final String description) {
    super("ProverEditor." + location + ": " + description);
  }
}
