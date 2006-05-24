//******************************************************************************
/* Copyright (c) 2004 INRIA. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: 
/*
/*******************************************************************************
/* Warnings/Remarks:
/******************************************************************************/

package jml2b.pog;

import jml2b.IJml2bConfiguration;
import jml2b.structure.java.JmlFile;

/**
 * This interface describes an obvious prover. It has to be implemented by plugin that
 * want to interact as obvious prover.
 * 
 * @author L. Burdy
 **/
public interface IObviousProver {

	/**
	 * Prove and save the status of a jpo file.
	 * @param config The current configuration
	 * @param file The JPO file
	 **/
	void prove(IJml2bConfiguration config, JmlFile file);
}
