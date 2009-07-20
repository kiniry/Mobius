//******************************************************************************
/* Copyright (c) 2004 INRIA. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: 
/*
/*******************************************************************************
/* Warnings/Remarks:
/******************************************************************************/

package jpov.structure;

import java.util.Arrays;
import java.util.Enumeration;
import java.util.Vector;

/**
 * @author lburdy
 *
 * To change the template for this generated type comment go to
 * Window&gt;Preferences&gt;Java&gt;Code Generation&gt;Code and Comments
 */
public class LemmaHierarchy extends TreeObject {

	boolean split = false;
	boolean termin = false;
	Lemma lemm;
	LemmaHierarchy one;
	LemmaHierarchy two;
	String text = "";

	LemmaHierarchy(Lemma[] lemmas) {
		boolean one = false;
		boolean two = false;
		Vector oneV = new Vector();
		Vector twoV = new Vector();
		for (int i = 0; i < lemmas.length; i++) {
			if (lemmas[i].getCaseNum().length() < 1 ||
					lemmas[i].getCaseNum().charAt(0) == '1') {
				one = true;
				oneV.add(lemmas[i]);
			} else if (lemmas[i].getCaseNum().charAt(0) == '2') {
				two = true;
				twoV.add(lemmas[i]);
			}
		}
		if (one && two) {
			split = true;
			termin = false;
			this.one = new LemmaHierarchy(oneV, "1", "Case 1");
			this.two = new LemmaHierarchy(twoV, "2", "Case 2");
		} else if (one) {
			split = false;
			termin = false;
			this.one = new LemmaHierarchy(oneV, "1", "Case 1");
		} else if (two) {
			split = false;
			termin = false;
			this.one = new LemmaHierarchy(twoV, "2", "Case 1");
		} else {
			split = false;
			termin = true;
			lemm = lemmas[0];
			lemm.setText("Case 1");
		}
	}

	private LemmaHierarchy(Vector lemmas, String prefix, String parent) {
		boolean one = false;
		boolean two = false;
		Vector oneV = new Vector();
		Vector twoV = new Vector();
		Enumeration e = lemmas.elements();
		while (e.hasMoreElements()) {
			Lemma l = (Lemma) e.nextElement();
			if (l.getCaseNum().indexOf(prefix + ".1") == 0) {
				one = true;
				oneV.add(l);
			} else if (l.getCaseNum().indexOf(prefix + ".2") == 0) {
				two = true;
				twoV.add(l);
			}
		}
		if (one && two) {
			text = parent; // + "." + prefix.charAt(prefix.length()-1);
			split = true;
			termin = false;
			this.one = new LemmaHierarchy(oneV, prefix + ".1", text + ".1");
			this.two = new LemmaHierarchy(twoV, prefix + ".2", text + ".2");
		} else if (one) {
			split = false;
			termin = false;
			this.one = new LemmaHierarchy(oneV, prefix + ".1", parent);
		} else if (two) {
			split = false;
			termin = false;
			this.one = new LemmaHierarchy(twoV, prefix + ".2", parent);
		} else {
			split = false;
			termin = true;
			lemm = (Lemma) lemmas.get(0);
			lemm.setText(parent /* + ".1"*/
			);
		}

	}

	public String getText(int type) {
		return text;
	}

	public void setChecked() {
		if (split) {
			one.setChecked();
			two.setChecked();
		} else if (termin) {
			lemm.setChecked();
		} else
			one.setChecked();
	}

	public void setUnchecked() {
		if (split) {
			one.setUnchecked();
			two.setUnchecked();
		} else if (termin) {
			lemm.setUnchecked();
		} else
			one.setUnchecked();
	}

	public int getNbPo() {
		if (split) {
			return one.getNbPo() + two.getNbPo();
		} else if (termin) {
			return lemm.getNbPo();
		} else
			return one.getNbPo();

	}

	public int getNbPoProved(String prover) {
		if (split) {
			return one.getNbPoProved(prover) + two.getNbPoProved(prover);
		} else if (termin) {
			return lemm.getNbPoProved(prover);
		} else
			return one.getNbPoProved(prover);
	}

	public int getNbPoProved() {
		if (split) {
			return one.getNbPoProved() + two.getNbPoProved();
		} else if (termin) {
			return lemm.getNbPoProved();
		} else
			return one.getNbPoProved();
	}

	public Object[] getLemmasWithPo() {
		if (split) {
			Object[] res = { one.getDeeper(), two.getDeeper()};
			return res;
		} else if (termin) {
			Lemma[] res = { lemm };
			return res;
		} else
			return one.getLemmasWithPo();
	}

	private Object getDeeper() {
		if (split)
			return this;
		else if (termin)
			return lemm;
		else
			return one.getDeeper();
	}

	void setParent(Object jf) {
		super.setParent(jf);
		if (split) {
			one.setParent(jf);
			two.setParent(jf);
		} else if (!termin)
			one.setParent(jf);

	}

	public Vector getHyp() {
		if (split) {
			Vector a = one.getHyp();
			a.retainAll(two.getHyp());
			return a;
		} else if (termin)
			return new Vector(Arrays.asList(lemm.getHyp()));
		else
			return one.getHyp();

	}

	public Vector getFlow() {
		if (split) {
			Vector a = one.getFlow();
			a.retainAll(two.getFlow());
			return a;
		} else if (termin)
			return new Vector(Arrays.asList(lemm.getFlow()));
		else
			return one.getFlow();

	}

}
