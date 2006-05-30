//******************************************************************************
/* Copyright (c) 2003, 2004 INRIA. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: 
/*
/*******************************************************************************
/* Warnings/Remarks:
/******************************************************************************/

package pvsPlugin;

import java.io.IOException;

import jml2b.exceptions.LoadException;
import jml2b.pog.IProverStatus;
import jml2b.pog.lemma.ProverStatus;
import jml2b.structure.java.IJmlFile;
import jml2b.util.JpoInputStream;
import jml2b.util.JpoOutputStream;

/**
 * @author lburdy
 *
 * To change the template for this generated type comment go to
 * Window&gt;Preferences&gt;Java&gt;Code Generation&gt;Code and Comments
 */
public class PvsProverStatus extends ProverStatus implements IProverStatus {

	public PvsProverStatus() {
		super();
	}

	public PvsProverStatus(JpoInputStream s)
		throws IOException, LoadException {
		proveState = s.readByte();
	}

	PvsProverStatus(boolean b) {
		if (b)
			setProved();
		else
			setUnproved();
	}

	/**
	 * Saves the goal status in the a 
	 * <a href="{@docRoot}/jpov/doc-files/jpo.html"> .jpo file</a>
	 * @param s The output stream for the jpo file
	 * @throws IOException
	 * @see NonObviousGoal#save(DataOutputStream, JmlFile, IJmlFile)
	 **/
	public void save(JpoOutputStream s) throws IOException {
		s.writeByte(proveState);
	}

	public ProverStatus factory() {
		return new PvsProverStatus();
	}

	public ProverStatus factory(JpoInputStream s)
		throws IOException, LoadException {
		return new PvsProverStatus(s);
	}

}
