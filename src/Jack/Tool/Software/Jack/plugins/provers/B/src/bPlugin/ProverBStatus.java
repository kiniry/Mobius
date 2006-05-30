//******************************************************************************
/* Copyright (c) 2002, 2003 GEMPLUS Software Research Labs. All Rights Reserved.
/* Copyright (c) 2003, 2004 INRIA. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: ProveButton.java
/*
/********************************************************************************
/* Warnings/Remarks:
/*******************************************************************************/
package bPlugin;

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
public class ProverBStatus extends ProverStatus implements IProverStatus {

	/**
	 * Proof force value that corresponds to an interactive proof.
	 **/
	public static final byte PROVEDUTIL = 4;

	/**
	 * Prove force of a goal. The prove force is relevant only when the status
	 * is <code>PROVED</code>. The prove force is a value between 0 and 4.
	 * The value 4 corresponds to <code>PROVEDUTIL</code>.
	 **/
	private byte proveForce;

	/**
	 * Prove script of a goal. The prove script is relevant only when the status
	 * is <code>PROVED</code> and the force is <code>PROVEDUTIL</code>.
	 * The script is the Atelier B proof command that proved this goal.
	 * The default value is the empty string.
	 **/
	private String methodList = "";

	public ProverBStatus() {
		super();
	}

	public ProverBStatus(byte force) {
		super();
		proveState = PROVED;
		proveForce = force;
	}

	public ProverBStatus(JpoInputStream s) throws IOException, LoadException {
		proveState = s.readByte();
		proveForce = s.readByte();
		methodList = s.readUTF();
	}

	public ProverStatus factory() {
		return new ProverBStatus();
	}
	
	public ProverStatus factory(JpoInputStream s) throws IOException, LoadException {
		return new ProverBStatus(s); 
	}

	/**
	 * Returns the string to write into the <i>pmi</i> file corresponding to the
	 * proof status.
	 * @return <code>Proved(force)</code> or <code>Unproved</code> depending of
	 * the proof state and the proof force.
	 **/
	public String getProveState() {
		if (proveState == PROVED)
			return "Proved("
				+ (proveForce == PROVEDUTIL ? "Util" : ("" + proveForce))
				+ ")";
		else
			return "Unproved";
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
		s.writeByte(proveForce);
		s.writeUTF(methodList);
	}

	/**
	 * Returns the proof script.
	 * @return <code>methodList</code>
	 */
	public String getMethodList() {
		return methodList;
	}

	/**
	 * Returns the prove force.
	 * @return <code>proveForce</code>
	 */
	public byte getProveForce() {
		return proveForce;
	}

	/**
	 * Sets the proof script.
	 * @param methodList The methodList to set
	 */
	public void setMethodList(String methodList) {
		this.methodList = methodList;
	}

	/**
	 * Sets the prove force.
	 * @param proveForce The prove force to set
	 */
	public void setProveForce(byte proveForce) {
		this.proveForce = proveForce;
	}

	public boolean isProved(int force) {
		return isProved() && proveForce == force;
	}

}
