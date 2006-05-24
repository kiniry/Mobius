//******************************************************************************
/* Copyright (c) 2002, 2003 GEMPLUS Software Research Labs. All Rights Reserved.
/* Copyright (c) 2003, 2004 INRIA. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: Goal
/*
/*******************************************************************************
/* Warnings/Remarks:
/*  09/26/2003 : Simplify integration achieved
/******************************************************************************/
package jpov.structure;

import java.io.IOException;

import jml2b.IJml2bConfiguration;
import jml2b.formula.Formula;
import jml2b.pog.lemma.GoalOrigin;
import jml2b.pog.lemma.ProverStatus;
import jml2b.structure.java.IJmlFile;
import jml2b.util.JpoInputStream;
import jml2b.util.JpoOutputStream;
import jpov.substitution.SubArrayElement;
import jpov.substitution.SubArrayElementSingle;
import jpov.substitution.SubArrayLength;
import jpov.substitution.SubForm;
import jpov.substitution.SubInstancesSet;
import jpov.substitution.SubInstancesSingle;
import jpov.substitution.SubMemberField;
import jpov.substitution.SubTmpVar;
import jpov.substitution.SubTypeofSet;
import jpov.substitution.SubTypeofSingle;
import jpov.substitution.Substitution;

/**
 * This class implements a goal.
 * @author L. Burdy
 **/
public class Goal extends TreeObject {

	/**
	 * Loads a substitution from a
	 * <a href="{@docRoot}/jpov/doc-files/jpo.html"> .jpo file</a>
	 * @param s The input stream corresponding to the jpo file.
	 * @return the loaded substitution.
	 **/
	private static Substitution loadSubstitution(
		IJml2bConfiguration config,
		IJmlFile fi,
		JpoInputStream s)
		throws IOException, jml2b.exceptions.LoadException {
		switch (s.readByte()) {
			case jml2b.pog.substitution.Substitution.ARRAY_ELEMENT :
				return new SubArrayElement(config, fi, s);
			case jml2b.pog.substitution.Substitution.ARRAY_ELEMENT_SINGLE :
				return new SubArrayElementSingle(config, fi, s);
			case jml2b.pog.substitution.Substitution.ARRAY_LENGTH :
				return new SubArrayLength(config, fi, s);
			case jml2b.pog.substitution.Substitution.FORM :
				return new SubForm(config, fi, s);
			case jml2b.pog.substitution.Substitution.INSTANCES_SET :
				return new SubInstancesSet(config, fi, s);
			case jml2b.pog.substitution.Substitution.INSTANCES_SINGLE :
				return new SubInstancesSingle(config, fi, s);
			case jml2b.pog.substitution.Substitution.TMP_VAR :
				return new SubTmpVar(config, fi, s);
			case jml2b.pog.substitution.Substitution.TYPEOF_SET :
				return new SubTypeofSet(config, fi, s);
			case jml2b.pog.substitution.Substitution.TYPEOF_SINGLE :
				return new SubTypeofSingle(config, fi, s);
			case jml2b.pog.substitution.Substitution.MEMBER_FIELD :
				return new SubMemberField(config, fi, s);
			default :
				throw new jml2b.exceptions.LoadException(
					"loadSubstitution : wrong type");
		}
	}

	/**
	 * The number associated with this goal into its englobing case.
	 **/
	private int goalNum;

	/**
	 * The number associated with this goal in the .po file of the Atelier B.
	 **/
	private int number;

	/**
	 * The proof status of the goal.
	 **/
	private jml2b.pog.lemma.GoalStatus state;

	/**
	 * The origin of the goal. Possible values are defined in {@link GoalStatus}
	 **/
	private byte origin;

	/**
	 * The origin of the goal. Possible values are defined in {@link GoalStatus}
	 **/
	private String comment;

	/**
	 * Formula that should be proved.
	 */
	private VirtualFormula vf;

	/**
	 * Array of substitutions applied to the goal.
	 **/
	private Substitution[] subs;

	/**
	 * The formula corresponding to the goal when it was created
	 **/
	private Formula original;

	/*@
	  @ private invariant state != null
	  @                && vf != null
	  @                && original != null
	  @                && subs != null;
	  @*/

	/**
	 * Constructs a goal from informations loaded into a 
	 * <a href="{@docRoot}/jpov/doc-files/jpo.html"> .jpo file</a>
	 * @param s The input stream 
	 * @param num The current goal number into the current case
	 * @throws IOException
	 * @throws LoadException
	 **/
	Goal(
		IJml2bConfiguration configuration,
		IJmlFile fi,
		JpoInputStream s,
		int num)
		throws IOException, jml2b.exceptions.LoadException {
		number = s.readInt();
		state = new jml2b.pog.lemma.GoalStatus(s);
		origin = s.readByte();
		comment = s.readUTF();
		vf = new VirtualFormula(configuration, fi, s);
		goalNum = num;
		original = Formula.create(configuration, s, fi);
		int size = s.readInt();
		subs = new Substitution[size];
		for (int i = 0; i < size; i++)
			subs[i] = loadSubstitution(configuration, fi, s);
	}

	/**
	 * @return Goal xx
	 **/
	public String getText(int type) {
		return "Goal " + goalNum;
	}

	/**
	 * @return <code>1</code> if the goal is proved, <code>0</code> otherwise
	 **/
	public int getNbPoProved(String prover) {
		return state.isProved(prover) ? 1 : 0;
	}

	/**
	 * @return <code>1</code> if the goal is proved, <code>0</code> otherwise
	 **/
	public int getNbPoProved() {
		return state.isProved() ? 1 : 0;
	}

	/**
	 * @return Goal 1
	 **/
	public int getNbPo() {
		return 1;
	}

	public boolean isProved(String prover) {
		return state.isProved(prover);
	}

	public boolean isChecked() {
		return state.isChecked();
	}

	/**
	 * Returns whether the goal is proven or checked.
	 * @return <code>true</code> if the goal is not unproved, 
	 * <code>false</code> otherwise
	 **/
	public boolean isMergeable() {
		return state.isChecked() || state.isProved();
	}
	/**
	 * Returns a string describing the goal origin.
	 **/
	public String getOriginString() {
		return GoalOrigin.getGoalTypeString(origin, comment);
	}

	/**
	 * Sets the goal status
	 * @param b The goal status to set
	 **/
	/*@
	  @ requires b != null;
	  @*/
	public void setStatus(String prover, ProverStatus b) {
		state.setStatus(prover, b);
	}

	public void setChecked() {
		state.setChecked();
	}

	public void setUnchecked() {
		state.setUnproved();
	}

	/**
	 * Sets the goal status to unprove.
	 **/
	void unprove() {
		state.setUnproved();
	}

	/**
	 * Saves the goal into a 
	 * <a href="{@docRoot}/jpov/doc-files/jpo.html"> .jpo file</a>
	 * @param s The .jpo  file output stream
	 * @throws IOException
	 **/
	void save(IJml2bConfiguration config, JpoOutputStream s, IJmlFile jf) throws IOException {
		s.writeInt(number);
		state.save(s);
		s.writeByte(origin);
		s.writeUTF(comment);
		vf.save(config, s, 0, jf);
		original.save(config, s, jf);
		s.writeInt(subs.length);
		for (int i = 0; i < subs.length; i++)
			subs[i].save(config, s, jf);
	}

	/**
	 * Returns the virtual formula.
	 * @return <code>vf</code>
	 */
	public VirtualFormula getVf() {
		return vf;
	}

	/**
	 * Returns the formula.
	 **/
	public Formula getFormula() {
		return vf.getF();
	}

	/**
	 * Returns the number associated with this goal in the .po file of the 
	 * Atelier B
	 * @return <code>number</code>
	 **/
	public int getNumber() {
		return number;
	}

	/**
	 * Returns the origin of the goal
	 * @return <code>origin</code>
	 **/
	public int getGoalType() {
		return origin;
	}

	public ProverStatus getProverStatus(String prover) {
		return state.getProverStatus(prover);
	}

	/**
	 * @return
	 */
	public Formula getOriginal() {
		return original;
	}

	/**
	 * @return
	 */
	public Substitution[] getSubs() {
		return subs;
	}

	/**
	 * @return
	 */
	public jml2b.pog.lemma.GoalStatus getState() {
		return state;
	}
	
	boolean selected = false;
	public void setSelected() {
		selected = true;
	}
	public void setUnselected() {
		selected = false;
	}

	/**
	 * @return
	 */
	public boolean isSelected() {
		return selected;
	}
	

}
