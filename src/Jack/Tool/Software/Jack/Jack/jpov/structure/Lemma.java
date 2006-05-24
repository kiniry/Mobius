//******************************************************************************
/* Copyright (c) 2002, 2003 GEMPLUS Software Research Labs. All Rights Reserved.
/* Copyright (c) 2003, 2004 INRIA. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: LemmaViewer
/*
/*******************************************************************************
/* Warnings/Remarks:
/*  09/26/2003 : Simplify integration achieved
/******************************************************************************/
package jpov.structure;

import jack.plugin.perspective.ICaseExplorer;

import java.io.IOException;
import java.util.ArrayList;

import jml2b.IJml2bConfiguration;
import jml2b.structure.java.IJmlFile;
import jml2b.util.JpoInputStream;
import jml2b.util.JpoOutputStream;
import jpov.viewer.source.Box;

/**
 * This class implements a node tree corresponding to a case.
 * @author L. Burdy
 **/
public class Lemma extends TreeObject {

	/**
	 * Loads a lemma from a 
	 * <a href="{@docRoot}/jpov/doc-files/jpo.html"> .jpo file</a> and set the 
	 * parent of its goal 
	 * @param s The input stream corresponding to the jpo file
	 * @param locHyp The array of current hypothesis
	 * @param num The number of the case into its englobing method
	 * @return the loaded lemma
	 **/
	static Lemma loadLemma(
		IJml2bConfiguration config,
		IJmlFile fi,
		JpoInputStream s,
		VirtualFormula[] locHyp,
		Box[] locFlow,
		int num)
		throws IOException, jml2b.exceptions.LoadException {
		Lemma l = new Lemma(config, fi, s, locHyp, locFlow, num);
		for (int j = 0; j < l.goals.length; j++)
			l.goals[j].setParent(l);

		return l;
	}

	/**
	 * The case number into its englobing method
	 **/
	private String caseNum;

	private int num;

	/**
	 * The name of the method to which this case belongs in the po file
	 **/
	private String name;
	private String text;

	/**
	 * The array of hypothesis of the goals
	 **/
	private VirtualFormula[] hyp;

	/**
	 * The array of goals
	 **/
	private jpov.structure.Goal[] goals;

	/**
	 * The array of boxes
	 **/
	private Box[] flow;

	/*@
	  @ private invariant name != null
	  @                && hyp != null
	  @                && goals != null
	  @                && flow != null;
	  @*/

	/**
	 * Constructs a lemma from a 
	 * <a href="{@docRoot}/jpov/doc-files/jpo.html"> .jpo file</a>.
	 * @param s The input stream corresponding to the jpo file
	 * @param locHyp The array of current hypothesis
	 * @param num The number of the case into its englobing method
	 **/
	private Lemma(
		IJml2bConfiguration config,
		IJmlFile fi,
		JpoInputStream s,
		VirtualFormula[] locHyp,
		Box[] locFlow,
		int num)
		throws IOException, jml2b.exceptions.LoadException {
		name = s.readUTF();
		caseNum = s.readUTF();
		hyp = new VirtualFormula[s.readInt()];
		for (int j = 0; j < hyp.length; j++) {
			int index = s.readInt();
			hyp[j] = findVf(locHyp, index);
		}
		goals = new jpov.structure.Goal[s.readInt()];
		for (int j = 0; j < goals.length; j++)
			goals[j] = new Goal(config, fi, s, j + 1);
		flow = new Box[s.readInt()];
		for (int j = 0; j < flow.length; j++) {
			int index = s.readInt();
			flow[j] = findFlow(locFlow, index);
		}
		this.num = num;
	}

	//	public boolean isProved() {
	//		boolean res = true;
	//		for (int i = 0; i < goals.length; i++)
	//			res &= goals[i].isProved();
	//		return res;
	//	}

	public void setChecked() {
		for (int i = 0; i < goals.length; i++)
			goals[i].setChecked();
	}

	public void setUnchecked() {
		for (int i = 0; i < goals.length; i++)
			goals[i].setUnchecked();
	}

	/**
	 * Saves the lemma into a 
	 * <a href="{@docRoot}/jpov/doc-files/jpo.html"> .jpo file</a>
	 * @param s The ouput stream corresponding to the jpo file
	 **/
	void save(IJml2bConfiguration config, JpoOutputStream s, IJmlFile jf) throws IOException {
		s.writeUTF(name);
		s.writeUTF(caseNum);
		s.writeInt(hyp.length);
		for (int i = 0; i < hyp.length; i++)
			s.writeInt(hyp[i].getIndex());
		s.writeInt(goals.length);
		for (int i = 0; i < goals.length; i++)
			goals[i].save(config, s, jf);
		s.writeInt(flow.length);
		for (int i = 0; i < flow.length; i++)
			s.writeInt(flow[i].getIndex());
	}

	/**
	 * Sets all the goals of this case to unprove.
	 **/
	void unprove() {
		for (int i = 0; i < goals.length; i++)
			goals[i].unprove();
	}

	/**
	 * Looks for a formula with a given index into a virtual formula array
	 * @param locHyp The array of formula with index
	 * @param ident The searched for index
	 * @return The first formula in the array with the given index
	 * @throws LoadException when no formula is found
	 **/
	private static VirtualFormula findVf(VirtualFormula[] locHyp, int index)
		throws jml2b.exceptions.LoadException {
		for (int i = 0; i < locHyp.length; i++) {
			if (locHyp[i].getIndex() == index)
				return locHyp[i];
		}
		throw new jml2b.exceptions.LoadException(
			"findVf ; cannot find " + index);
	}

	private static Box findFlow(Box[] locFlow, int index)
		throws jml2b.exceptions.LoadException {
		for (int i = 0; i < locFlow.length; i++) {
			if (locFlow[i].getIndex() == index)
				return locFlow[i];
		}
		throw new jml2b.exceptions.LoadException(
			"findFlow: cannot find " + index);
	}

	public int getNbPo() {
		return goals.length;
	}

	public int getNbPoProved() {
		int res = 0;
		for (int i = 0; i < goals.length; i++)
			if (goals[i].isProved())
				res++;
		return res;
	}

	public int getNbPoProved(String prover) {
		int res = 0;
		for (int i = 0; i < goals.length; i++)
			if (goals[i].isProved(prover))
				res++;
		return res;
	}

	public int getNbCheckedPo() {
		int res = 0;
		for (int i = 0; i < goals.length; i++)
			if (goals[i].isChecked())
				res++;
		return res;
	}

	//	/**
	//	 * Prints the theory ProofState of the pmi file containing the proof status 
	//	 * of the set of goals
	//	 * @param stream the print stream corresponding to the pmi file
	//	 * @param firstItem indicates whether a line has already been wroten
	//	 * @return whether a line has already been wroten
	//	 **/
	//	boolean printProofState(PrintStream stream, boolean firstItem) {
	//		for (int i = goals.length - 1; i >= 0; i--) {
	//
	//			if (firstItem)
	//				firstItem = false;
	//			else
	//				stream.println(";");
	//			stream.print(goals[i].getProverBStatus().proofState());
	//		}
	//		return firstItem;
	//	}

	//	/**
	//	 * Prints the theory MEthodList of the pmi file containing the proof script 
	//	 * of the set of goals
	//	 * @param stream the print stream corresponding to the pmi file
	//	 * @param firstItem indicates whether a line has already been wroten
	//	 * @return whether a line has already been wroten
	//	 **/
	//	boolean printMethodList(PrintStream stream, boolean firstItem) {
	//		for (int i = goals.length - 1; i >= 0; i--) {
	//			if (firstItem)
	//				firstItem = false;
	//			else
	//				stream.println(";");
	//			if (goals[i].isProved()
	//				&& goals[i].getProverBStatus().getProveForce()
	//					== ProverBStatus.PROVEDUTIL)
	//				stream.print(goals[i].getProverBStatus().getMethodList());
	//			else
	//				stream.print("pr");
	//		}
	//		return firstItem;
	//	}

	//	/**
	//	 * Declares the variable and the hypothesis of the lemma in a coq file
	//	 * @param s The print stream corresponding to the coq file
	//	 **/
	//	void export2Coq(PrintStream s) throws LanguageException {
	//		for (int i = 0; i < hyp.length; i++) {
	//			if (hyp[i].getF().getNodeType() == FormToken.LOCAL_VAR_DECL) {
	//				s.println(
	//					"Variable "
	//						+ ((BinaryForm) hyp[i].getF())
	//							.toLang("Coq", 0)
	//							.toUniqString()
	//						+ ".");
	//			}
	//		}
	//		for (int i = 0; i < hyp.length; i++) {
	//			s.println("Definition h_" + (i + 1) + " : Prop := ");
	//			s.println("   " + hyp[i].toCoq() + ".");
	//		}
	//	}

	/**
	 * @return Case xx
	 **/
	public String getText(int type) {
		if (type == ICaseExplorer.HIERARCHY)
			return text;
		else
			return "Case " + num;
	}

	/**
	 * Returns the case number into its englobing method.
	 * @return <code>caseNum</code>
	 **/
	public String getCaseNum() {
		return caseNum;
	}

	/**
	 * Returns the array of goals
	 * @return <code>goals</code>
	 **/
	public jpov.structure.Goal[] getGoals() {
		return goals;
	}

	/**
	 * Returns the name of the method to which this case belongs.
	 * @return <code>name</code>
	 **/
	public String getName() {
		return name;
	}

	/**
	 * Returns the array of boxes.
	 * @return <code>flow</code>
	 */
	public Box[] getFlow() {
		return flow;
	}

	/**
	 * Returns the array of hypothesis.
	 * @return <code>hyp</code>
	 */
	public VirtualFormula[] getHyp() {
		return hyp;
	}

	public void setText(String parent) {
		text = parent;
	}

	/**
	 * @return
	 */
	public int getNum() {
		return num;
	}

	public void addGoals(ArrayList al) {
		for (int i = 0; i < goals.length; i++)
			al.add(goals[i]);
	}
	
	public void selectAll() {
		for (int i = 0; i < goals.length; i++) {
			goals[i].setSelected();
		}
	}

}
