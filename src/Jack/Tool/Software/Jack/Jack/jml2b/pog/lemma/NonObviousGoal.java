//******************************************************************************
/* Copyright (c) 2002, 2003 GEMPLUS Software Research Labs. All Rights Reserved.
/* Copyright (c) 2003, 2004 INRIA. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: NonObviousGoal
/*
/*******************************************************************************
/* Warnings/Remarks:
/*  09/26/2003 : Simplify integration achieved
/******************************************************************************/
package jml2b.pog.lemma;

import java.io.IOException;
import java.util.Enumeration;
import java.util.Vector;

import jml2b.IJml2bConfiguration;
import jml2b.formula.Formula;
import jml2b.pog.substitution.Substitution;
import jml2b.structure.java.JmlFile;
import jml2b.util.JpoOutputStream;

/**
 * This class implements a non obvious goal, that is a goal that will be saved
 * in the JPO file.
 * @author L. Burdy
 */
public class NonObviousGoal extends Goal {

	/**
	 * The number associated with this goal in the .po file of the Atelier B.
	 **/
	private int number;

	/**
	 * The proof status of the goal.
	 **/
	private GoalStatus state;

	/*@
	  @ private invariant state != null;
	  @*/

	public NonObviousGoal() {
		
	}
	
	/**
	 * Constructs a non obvious goal from a goal with a goal status to 
	 * <i>unproved</i>.
	 * @param g The goal
	 **/
	public NonObviousGoal(Goal g) {
		super(
			g.getOrigin(),
			new Vector(),
			g.getVirtualFormula(),
			g.getOriginalFormula(),
			g.getSubs(),
			g.isOriginal());
		state = new GoalStatus();
	}

	/**
	 * Returns whether this goal is proven.
	 * @return <code>true</code> if the goal is proved, <code>false</code> 
	 * otherwise
	 **/
	public boolean isProved(String prover) {
		return state.isProved(prover);
	}

	/**
	 * Returns whether this goal is proven.
	 * @return <code>true</code> if the goal is proved, <code>false</code> 
	 * otherwise
	 **/
	public boolean isProved() {
		return state.isProved();
	}

	public boolean isChecked() {
		return state.isChecked();
	}

	/**
	 * Sets the goal number
	 * @param i The goal number
	 **/
	public int setNumber(int i) {
		return number = i;
	}

	/**
	 * Compares the goal with a set of possible loaded goals. If the goals merge, 
	 * the goal state is updated with the loaded goal.
	 * @param e The set of loaded goals.
	 * @throws MergeException
	 **/
	//@ requires jf != null;
	public void mergeWith(jpov.structure.Goal e) {
		if (e.isMergeable() && merge(e)) {
			state = e.getState();
		}
	}

	/**
	 * Returns whether the goal merges with another.
	 * @param g The tested goal
	 * @throws MergeException
	 **/
	//@ requires g != null;
	private boolean merge(jpov.structure.Goal g) {
		return getVirtualFormula().getFormula().is(g.getFormula());
	}

	/**
	 * Returns the goal
	 * @return the formula corresponding to the goal
	 **/
	public Formula getFormula() {
		return vf.getFormula();
	}
	/**
	 * Saves the goal in a 
	 * <a href="{@docRoot}/jpov/doc-files/jpo.html"> .jpo file</a>
	 * @param s The ouput stream representing the jpo file.
	 * @param jf The current JML file
	 * @throws IOException
	 **/
	//@ requires s != null;
	public void save(IJml2bConfiguration config, JpoOutputStream s, JmlFile jf) throws IOException {
		s.writeInt(number);
		state.save(s);
		getOrigin().save(s);
		getVirtualFormula().save(config, s, 0, jf);
		getOriginalFormula().save(config, s, jf);
		s.writeInt(getSubs().size());
		Enumeration e = getSubs().elements();
		while (e.hasMoreElements()) {
			Substitution element = (Substitution) e.nextElement();
			element.save(config, s, jf);
		}
	}

}
