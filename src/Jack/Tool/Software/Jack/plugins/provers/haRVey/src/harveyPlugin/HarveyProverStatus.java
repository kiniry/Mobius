//******************************************************************************
/* Copyright (c) 2003, 2004 INRIA. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: 
/*
/*******************************************************************************
/* Warnings/Remarks:
/******************************************************************************/
package harveyPlugin;

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
public class HarveyProverStatus extends ProverStatus implements IProverStatus {

	public HarveyProverStatus() {
		super();
	}

	public HarveyProverStatus(JpoInputStream s)
		throws IOException, LoadException {
		proveState = s.readByte();
	}

	HarveyProverStatus(boolean b) {
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

	/* (non-Javadoc)
	 * @see jml2b.languages.java.IProverStatus#factory()
	 */
	public ProverStatus factory() {
		return new HarveyProverStatus();
	}

	/* (non-Javadoc)
	 * @see jml2b.languages.java.IProverStatus#factory(java.io.DataInputStream)
	 */
	public ProverStatus factory(JpoInputStream s)
		throws IOException, LoadException {
		return new HarveyProverStatus(s);
	}

}
