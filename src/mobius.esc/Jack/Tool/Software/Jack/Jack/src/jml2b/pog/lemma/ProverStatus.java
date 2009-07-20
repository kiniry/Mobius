//******************************************************************************
/* Copyright (c) 2003, 2004 INRIA. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: 
/*
/*******************************************************************************
/* Warnings/Remarks:
/******************************************************************************/
package jml2b.pog.lemma;

import java.io.IOException;

import jml2b.util.JpoOutputStream;

/**
 * @author L. Burdy
 */
public abstract class ProverStatus {

	/**
	 * Proof state value that corresponds to a goal that is not proved neither
	 * checked.
	 **/
	public static final byte UNPROVED = 0;

	/**
	 * Proof state value that corresponds to a goal that is proved.
	 **/
	public static final byte PROVED = 1;

	/**
	 * Prove status of a goal. The status can be <code>UNPROVED</code>,
	 * <code>PROVED</code> or <code>CHECKED</code>.
	 * By default the status is <code>UNPROVED</code>.
	 **/
	protected byte proveState = UNPROVED;

	/**
	 * Sets the proof state to <code>PROVED</code>.
	 **/
	protected void setProved() {
		proveState = PROVED;
	}

	/**
	 * Sets the proof state to <code>UNPROVED</code>.
	 **/
	public void setUnproved() {
		proveState = UNPROVED;
	}

	/**
	 * Tests whether the goal is proved or not
	 * @return <code>true</code> if the proof state is <code>PROVED</code>, 
	 * <code>false</code> otherwise
	 **/
	public boolean isProved() {
		return proveState == PROVED;
	}

	/**
	 * Tests whether the goal is unproved or not.
	 * @return <code>true</code> if the proof state is <code>UNPROVED</code>, 
	 * <code>false</code> otherwise
	 **/
	public boolean isUnproved() {
		return proveState == UNPROVED;
	}

	/**
	 * Saves the goal status in the a 
	 * <a href="{@docRoot}/jpov/doc-files/jpo.html"> .jpo file</a>
	 * @param s The output stream for the jpo file
	 * @throws IOException
	 * @see NonObviousGoal#save(DataOutputStream, JmlFile, IJmlFile)
	 **/
	public abstract void save(JpoOutputStream s) throws IOException;

}
