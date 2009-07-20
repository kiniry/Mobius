//******************************************************************************
/* Copyright (c) 2003, 2004 INRIA. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: 
/*
/*******************************************************************************
/* Warnings/Remarks:
/******************************************************************************/
package jml2b.pog.proofobligation;

import jml2b.IJml2bConfiguration;
import jml2b.exceptions.Jml2bException;
import jml2b.exceptions.PogException;
import jml2b.util.Profiler;

/**
 * This abstract class describes a proof obligation and facilities to calculate 
 * them.
 * 
 * @author L. Burdy
 **/
public abstract class ProofObligation extends Profiler {

	/**
	 * Process the WP calculus on the proof obligations.
	 * @param config The current configuration
	 * @throws PogException
	 **/
	public abstract void pog(IJml2bConfiguration config)
		throws Jml2bException, PogException;

	/**
	 * Proves the obvious goals if asked.
	 * Cast all the remaining lemmas in {@link SimpleLemma}.
	 * This task is performed at the end of the WP calculus.
	 * @param prove indicate whether obvious goals should be suppressed from 
	 * the theorems
	 **/
	public abstract void proveObvious(boolean prove);

	/**
	 * @return the name to display in the progress monitor.
	 **/
	public abstract String getDisplayedName();
	
}
