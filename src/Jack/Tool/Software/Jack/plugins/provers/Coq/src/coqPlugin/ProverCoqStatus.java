//******************************************************************************
/* Copyright (c) 2003, 2004 INRIA. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: 
/*
/*******************************************************************************
/* Warnings/Remarks:
/******************************************************************************/
package coqPlugin;

import java.io.IOException;
import java.io.PrintStream;

import jml2b.exceptions.LoadException;
import jml2b.pog.IProverStatus;
import jml2b.pog.lemma.ProverStatus;
import jml2b.util.JpoInputStream;
import jml2b.util.JpoOutputStream;

/**
 * @author lburdy
 *
 * To change the template for this generated type comment go to
 * Window&gt;Preferences&gt;Java&gt;Code Generation&gt;Code and Comments
 */
public class ProverCoqStatus extends ProverStatus implements IProverStatus {
	private CoqFile file;
	private static final byte UNKNOWN = 0;
	private static final byte INTERACTIVE = 1;
	private static final byte AUTOMATIC = 2;
	private byte status;
	public ProverCoqStatus() {
		super();
		status = UNKNOWN;
	}

	public ProverCoqStatus(JpoInputStream s)
		throws IOException, LoadException {
		status = s.readByte();
		proveState = s.readByte();
//		if (status == INTERACTIVE)
//			file = CoqFile.load(s);
	}
	public ProverCoqStatus(boolean b) {
		status = AUTOMATIC;
		if (b)
			setProved();
		else
			setUnproved();
	}

	public ProverCoqStatus(boolean b, CoqFile f) {
		status = INTERACTIVE;
		if (b)
			setProved();
		else
			setUnproved();
		file = f;
	}

	/**
	 * Saves the goal status in the a 
	 * <a href="{@docRoot}/jpov/doc-files/jpo.html"> .jpo file</a>
	 * @param s The output stream for the jpo file
	 * @throws IOException
	 * @see NonObviousGoal#save(DataOutputStream, JmlFile)
	 **/
	public void save(JpoOutputStream s) throws IOException {
		s.writeByte(status);
		s.writeByte(proveState);
		//if (proveState == ) {
//		if (status == INTERACTIVE)
//			file.save(s);
//		//}
	}

	/* (non-Javadoc)
	 * @see jml2b.languages.java.IProverStatus#factory()
	 */
	public ProverStatus factory() {
		return new ProverCoqStatus();
	}

	/* (non-Javadoc)
	 * @see jml2b.languages.java.IProverStatus#factory(java.io.DataInputStream)
	 */
	public ProverStatus factory(JpoInputStream s)
		throws IOException, LoadException {
		return new ProverCoqStatus(s);
	}

	public String toString() {
		if (proveState == PROVED){
			if (status == AUTOMATIC) 
				return "The goal was proved automatically.";
			else 
				return "The goal was proved interactively.";
		}
		else {
			return "Goal unproved.";
		}
	}

	/**
	 * @param stream
	 */
	public void writeCoqToStream(PrintStream stream) {
		stream.print(file);
		
	}
	public boolean isUnknown() {
		return status == UNKNOWN;
	}
}
