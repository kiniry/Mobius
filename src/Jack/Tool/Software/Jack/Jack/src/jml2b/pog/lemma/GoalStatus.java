//******************************************************************************
/* Copyright (c) 2002, 2003 GEMPLUS Software Research Labs. All Rights Reserved.
/* Copyright (c) 2003, 2004 INRIA. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: GoalStatus.java
/*
/*******************************************************************************
/* Warnings/Remarks:
/*  09/26/2003 : Simplify integration achieved
/******************************************************************************/
package jml2b.pog.lemma;

import java.io.IOException;
import java.util.Enumeration;

import jml2b.exceptions.LoadException;
import jml2b.languages.Languages;
import jml2b.util.JpoInputStream;
import jml2b.util.JpoOutputStream;
import jml2b.util.Profiler;

/**
 * This class provides constants and facilities to manage the status of a goal.
 * @author L. Burdy
 */
public class GoalStatus extends Profiler {

	private ProverStatus[] ps;

	private boolean checked = false;

	/**
	 * Constructs by default a <i>goal status</i>.
	 * The state will be <code>UNPROVED</code>.
	 **/
	public GoalStatus() {
		ps = new ProverStatus[Languages.getNbLanguages()];
		Enumeration e = Languages.getLanguagesNames();
		while (e.hasMoreElements()) {
			String name = (String) e.nextElement();
			if (Languages.getProverStatusClass(name) != null)
				ps[Languages.getIndex(name)] =
					Languages.getProverStatusClass(name).factory();
		}
	}

	/**
	 * Constructs a non obvious goal from a
	 * <a href="{@docRoot}/jpov/doc-files/jpo.html"> .jpo file</a>
	 * @throws IOEXception
	 * @throws LoadException
	 **/
	public GoalStatus(JpoInputStream s) throws IOException, LoadException {
		checked = s.readBoolean();
		ps = new ProverStatus[Languages.getNbLanguages()];
		Enumeration e = Languages.getLanguagesNames();
		while (e.hasMoreElements()) {
			String name = (String) e.nextElement();
			if (Languages.getProverStatusClass(name) != null)
				ps[Languages.getIndex(name)] =
					Languages.getProverStatusClass(name).factory(s);
		}
	}

	/**
	 * Sets the proof state to <code>PROVED</code>.
	 **/
	public void setProved(int prover) {
		ps[prover].setProved();
		checked = false;
	}

	/**
	 * Sets the proof state to <code>CHECKED</code>.
	 **/
	public void setChecked() {
		checked = true;
	}

	/**
	 * Sets the proof state to <code>UNPROVED</code>.
	 **/
	public void setUnproved() {
		checked = false;
		for (int i = 0; i < ps.length; i++)
			if (ps[i] != null)
				ps[i].setUnproved();
	}

	public boolean isProved(String prover) {
		return ps[Languages.getIndex(prover)].isProved();
	}

	public boolean isProved() {
		boolean res = false;
		for (int i = 0; i < ps.length; i++)
			if (ps[i] != null)
				res = res || ps[i].isProved();
		return res;
	}

	/**
	 * Tests whether the goal is checked or not.
	 * @return <code>true</code> if the proof state is <code>CHECKED</code>, 
	 * <code>false</code> otherwise
	 **/
	public boolean isChecked() {
		return checked;
	}

	/**
	 * Saves the goal status in the a 
	 * <a href="{@docRoot}/jpov/doc-files/jpo.html"> .jpo file</a>
	 * @param s The output stream for the jpo file
	 * @throws IOException
	 * @see NonObviousGoal#save(DataOutputStream, JmlFile, IJmlFile)
	 **/
	public void save(JpoOutputStream s) throws IOException {
		s.writeBoolean(checked);
		for (int i = 0; i < ps.length; i++)
			if (ps[i] != null)
				ps[i].save(s);
	}

	/**
	 * Returns the prove force.
	 * @return <code>proveForce</code>
	 */
	public ProverStatus getProverStatus(String name) {
		return ps[Languages.getIndex(name)];
	}

	public void setStatus(String prover, ProverStatus ps) {
		checked = false;
		this.ps[Languages.getIndex(prover)] = ps;
	}
}
