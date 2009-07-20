//******************************************************************************
/* Copyright (c) 2002, 2003 GEMPLUS Software Research Labs. All Rights Reserved.
/* Copyright (c) 2003, 2004 INRIA. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: Proofs
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
 * This class implements a node in the tree corresponding to the static 
 * initialization. For the methods, it does not correspond to a node, it is
 * overpassed to display lemmas. Nevertheless it contains the array of 
 * hypothesis that are cited in the methods lemmas
 * @author L. Burdy
 **/
public class Proofs extends TreeObject {

	/**
	 * The array of hypothesis that are referenced in the lemmas
	 **/
	private VirtualFormula[] locHyp;

	private Box[] locFlow;

	/**
	 * The array of lemmas
	 **/
	private Lemma[] lemmas;

	private LemmaHierarchy lemmaHierarchy;

	/*@
	  @ private invariant locHyp != null
	  @                && lemmas != null;
	  @*/

	/**
	 * Constructs a proof from a 
	 * <a href="{@docRoot}/jpov/doc-files/jpo.html"> .jpo file</a>
	 * @param s The input stream corresponding to the JPO file
	 **/
	Proofs(IJml2bConfiguration config, IJmlFile fi, JpoInputStream s)
		throws IOException, jml2b.exceptions.LoadException {
		locHyp = new VirtualFormula[s.readInt()];
		for (int j = 0; j < locHyp.length; j++)
			locHyp[j] = new VirtualFormula(config, fi, s);
		locFlow = new Box[s.readInt()];
		for (int j = 0; j < locFlow.length; j++)
			locFlow[j] = new Box(s);
		lemmas = new Lemma[s.readInt()];
		for (int j = 0; j < lemmas.length; j++)
			lemmas[j] = Lemma.loadLemma(config, fi, s, locHyp, locFlow, j + 1);
		if (lemmas.length > 0)
			lemmaHierarchy = new LemmaHierarchy(lemmas);
	}

	/**
	 * Returns an array containing lemmas with almost one goal
	 * @return a subarray of the lemmas array
	 **/
	public Object[] getLemmasWithPo(int type) {
		if (type == ICaseExplorer.HIERARCHY) {
			if (lemmaHierarchy != null)
				return lemmaHierarchy.getLemmasWithPo();
			else
				return new Object[0];
		} else {
			int j = 0;
			for (int i = 0; i < lemmas.length; i++)
				if (lemmas[i].getNbPo() > 0)
					j++;
			Lemma res[] = new Lemma[j];
			j = 0;
			for (int i = 0; i < lemmas.length; i++)
				if (lemmas[i].getNbPo() > 0)
					res[j++] = lemmas[i];
			return res;
		}
	}

	void setParent(Object o) {
		super.setParent(o);
		for (int i = 0; i < lemmas.length; i++)
			lemmas[i].setParent(o);
		if (lemmaHierarchy != null)
			lemmaHierarchy.setParent(o);
	}

	public void setChecked() {
		for (int i = 0; i < lemmas.length; i++)
			lemmas[i].setChecked();
	}

	public void setUnchecked() {
		for (int i = 0; i < lemmas.length; i++)
			lemmas[i].setUnchecked();
	}

//	public boolean isProved() {
//		boolean res = true;
//		for (int i = 0; i < lemmas.length; i++) {
//			res &= lemmas[i].isProved();
//		}
//		return res;
//	}

	/**
	 * Saves the proofs into a 
	 * <a href="{@docRoot}/jpov/doc-files/jpo.html"> .jpo file</a>
	 * @param s The output stream corresponding to the file
	 **/
	void save(IJml2bConfiguration config, JpoOutputStream s, IJmlFile jf) throws IOException {
		s.writeInt(locHyp.length);
		for (int i = 0; i < locHyp.length; i++) {
			locHyp[i].save(config, s, i, jf);
		}
		s.writeInt(locFlow.length);
		for (int i = 0; i < locFlow.length; i++) {
			locFlow[i].save(s, i);
		}
		s.writeInt(lemmas.length);
		for (int i = 0; i < lemmas.length; i++) {
			lemmas[i].save(config, s, jf);
		}
	}

	/**
	 * Sets all the goals of this case to unprove.
	 **/
	void unprove() {
		for (int i = 0; i < lemmas.length; i++) {
			lemmas[i].unprove();
		}
	}

	public int getNbPo() {
		int res = 0;
		for (int i = 0; i < lemmas.length; i++) {
			res += lemmas[i].getNbPo();
		}
		return res;
	}

	public int getNbPoProved() {
		int res = 0;
		for (int i = 0; i < lemmas.length; i++) {
			res += lemmas[i].getNbPoProved();
		}
		return res;
	}

	public int getNbPoProved(String prover) {
		int res = 0;
		for (int i = 0; i < lemmas.length; i++) {
			res += lemmas[i].getNbPoProved(prover);
		}
		return res;
	}

	public int getNbCheckedPo() {
		int res = 0;
		for (int i = 0; i < lemmas.length; i++) {
			res += lemmas[i].getNbCheckedPo();
		}
		return res;
	}

	public String getText(int type) {
		return null;
	}

	/**
	 * Return the lemmas array
	 * @return <code>lemmas</code>
	 **/
	public Lemma[] getLemmas() {
		return lemmas;
	}

	public void addGoals(ArrayList al) {
		for (int i = 0; i < lemmas.length; i++) {
			lemmas[i].addGoals(al);
		}
	}

}
