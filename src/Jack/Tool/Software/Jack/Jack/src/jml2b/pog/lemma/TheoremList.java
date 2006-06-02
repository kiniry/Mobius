//******************************************************************************
/* Copyright (c) 2002, 2003 GEMPLUS Software Research Labs. All Rights Reserved.
/* Copyright (c) 2003, 2004 INRIA. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: TheoremList.java
/*
/*******************************************************************************
//* Warnings/Remarks:
/******************************************************************************/
package jml2b.pog.lemma;

import java.io.IOException;
import java.util.Enumeration;
import java.util.Set;
import java.util.Vector;

import jml2b.IJml2bConfiguration;
import jml2b.exceptions.WrongLabelException;
import jml2b.formula.Formula;
import jml2b.pog.substitution.Substitution;
import jml2b.pog.util.ColoredInfo;
import jml2b.structure.java.AClass;
import jml2b.structure.java.Field;
import jml2b.structure.java.JmlFile;
import jml2b.structure.java.Type;
import jml2b.util.JpoOutputStream;
import jml2b.util.Profiler;

/**
 * This class implements a list of theorems
 * @author L. Burdy
 */
public class TheoremList extends Profiler {

	/**
	 * The current theorem
	 **/
	private Theorem th;

	/**
	 * The next element of the list
	 **/
	private TheoremList next;

	/*@
	  @ private invariant th != null;
	  @*/

	/**
	 * Construct a list of theorems from a set of theorems
	 * @param theorems The set of theorems
	 **/
	TheoremList(Enumeration theorems) {
		th = (Theorem) theorems.nextElement();
		if (theorems.hasMoreElements())
			next = new TheoremList(theorems);
		else
			next = null;
	}

	/**
	 * Constructs a list that contains one theorem corresponding to a lemma
	 * @param l The lemma
	 **/
	TheoremList(Lemma l) {
		th = new Theorem(l);
	}

	/**
	 * Constructs a list that contains one theorem
	 * @param l The theorem
	 **/
	/*@
	  @ requires t != null;
	  @*/
	TheoremList(Theorem t) {
		th = t;
	}

	/**
	 * Constructs a list from another list
	 * @param t The head of the list
	 * @param l The tail of the list
	 **/
	/*@
	  @ requires t != null;
	  @*/
	private TheoremList(Theorem t, TheoremList l) {
		th = t;
		next = l;
	}

	/**
	 * Clones the theorem list
	 * @return the cloned theorem list
	 **/
	public Object clone() {
		return new TheoremList(
			(Theorem) th.clone(),
			next == null ? null : (TheoremList) next.clone());
	}

	/**
	 * Concats two lists
	 * @param theoremList The list to concat
	 **/
	void addAll(TheoremList theoremList) {
		TheoremList tmp = this;
		while (tmp.next != null)
			tmp = tmp.next;
		tmp.next = theoremList;
	}

	/**
	 * Assign a name to the lemmas contained in the list
	 * @param name The name to assign
	 **/
	void setName(String name) {
		th.setName(name);
		if (next != null)
			next.setName(name);
	}

	/**
	 * Suppress the <i>Called Old</i> expressions in the list.
	 * @return the current list when the <i>Called Old</i> have been 
	 * suppressed.
	 **/
	void suppressSpecialOld(int token) {
		th.suppressSpecialOld(token);
		if (next != null)
			next.suppressSpecialOld(token);
	}

	/**
	 * Adds a new hypothese to each theorem of the list.
	 * If the hypothesis is <code>false</code> the hypothese is not added and
	 * all the lemmas are removed.
	 * @param vf hypothese to add
	 * @return <code>true</code> if the hypothese has been added, 
	 * <code>false</code> otherwise
	 **/
	boolean addHyp(VirtualFormula vf) {
		boolean res = th.addHyp(vf);
		if (next != null)
			res = next.addHyp(vf) || res;
		return res;
	}

	/**
	 * Substitue in the theorems a hypothese by another.
	 * In theorems, hypothesis are pointer to the hypothesis of 
	 * {@link Proofs#locHyp}. When an hypothese is changed in 
	 * {@link Proofs#locHyp}, the pointer should be changed in the theorem to 
	 * point to the new hypothese.
	 * @param vf old hypothese
	 * @param newVf new hypothese
	 **/
	void subHyp(VirtualFormula vf, VirtualFormula newVf) {
		th.subHyp(vf, newVf);
		if (next != null)
			next.subHyp(vf, newVf);
	}

	void subFlow(ColoredInfo vf, ColoredInfo newVf) {
		th.subFlow(vf, newVf);
		if (next != null)
			next.subFlow(vf, newVf);
	}

	/**
	 * Test wheter an hypothesis is used in the theorems.
	 * @param vf the tested hypothese.
	 * @return <code>true</code> if the hypothese is pointed by a theorem
	 * <code>false</code> otherwise.
	 **/
	boolean isUsed(VirtualFormula vf) {
		boolean res = th.isUsed(vf);
		if (next != null)
			res = next.isUsed(vf) || res;
		return res;
	}

	/**
	 * Returns the number of goals (or proof obligations).
	 * @return the number of goals of the theorem list
	 **/
	int nbPo() {
		int res = th.nbPo();
		if (next != null)
			res += next.nbPo();
		return res;
	}

	int nbPoChecked() {
		int res = th.nbPoChecked();
		if (next != null)
			res += next.nbPoChecked();
		return res;
	}
	
	/**
	 * Returns the number of goals that are in a specified state.
	 * @param state state of the whished goals number
	 * @return the number of goals of the theorem list which have a state 
	 * equals to the paremeter.
	 **/
	int nbPoProved(String prover) {
		int res = th.nbPoProved(prover);
		if (next != null)
			res += next.nbPoProved(prover);
		return res;
	}

	/**
	 * Returns the number of goals that are in a specified state.
	 * @param state state of the whished goals number
	 * @return the number of goals of the theorem list which have a state 
	 * equals to the paremeter.
	 **/
	int nbPoProved() {
		int res = th.nbPoProved();
		if (next != null)
			res += next.nbPoProved();
		return res;
	}

	/**
	 * Adds a <i>colored info</i> to the theorems of the list.
	 * @param b The added colored info
	 **/
	void addBox(ColoredInfo b) {
		th.addBox(b);
		if (next != null)
			next.addBox(b);
	}

	/**
	 * Returns the number of lemmas in the theorem list
	 **/
	public int nbLemmas() {
		int res = th.nbLemmas();
		if (next != null)
			res += next.nbLemmas();
		return res;
	}

	/**
	 * Returns the number of theorems in the theorem list
	 **/
	public int nbTheorems() {
		if (next != null)
			return 1 + next.nbTheorems();
		else
			return 1;
	}

	/**
	 * Returns a lemma of a theorem of the list
	 * @param i The index of the searched lemma
	 * @return The ith lemma of the theorem list
	 **/
	public SimpleLemma getLemma(int i) {
		int tmp = th.nbLemmas();
		if (i < tmp)
			return th.getLemma(i);
		else
			return next.getLemma(i - tmp);
	}

	/**
	 * Returns a theoram of the list
	 * @param i The index of the searched theorem
	 * @return The ith theorem of the list
	 **/
	public Theorem getTheorem(int i) {
		int tmp = th.nbLemmas();
		if (i < tmp)
			return th;
		else
			return next.getTheorem(i - tmp);
	}

	/**
	 * Saves the theorem list in a 
	 * <a href="{@docRoot}/jpov/doc-files/jpo.html"> .jpo file</a>
	 * @param s output stream for the jpo file
	 * @param jf current {@link JmlFile}
	 **/
	void save(IJml2bConfiguration config, JpoOutputStream s, JmlFile jf) throws IOException {
		th.save(config, s, jf);
		if (next != null)
			next.save(config, s, jf);
	}

	/**
	 * Merge two list of theorems.
	 * @param theoremlist The loaded theorem list merged with the current one
	 **/
	void mergeWith(jpov.structure.Lemma[] theoremList) {
		for (int i=0; i < theoremList.length; i++) {
			th.mergeWith(theoremList[i]);
		} 
		if (next != null)
			next.mergeWith(theoremList);

	}

	/**
	 * Annotates all the fields that appear in the theorem list to declare them 
	 * in the Atelier B files.
	 **/
	void garbageIdent() {
		th.garbageIdent();
		if (next != null)
			next.garbageIdent();
	}

	/**
	 * Apply a substitution to the theorem list.
	 * @param s substitution to apply.
	 * @return the current theorem list substituted.
	 **/
	public void sub(Substitution s) {
		th.sub(s);
		if (next != null)
			next.sub(s);
	}

	Vector newHyp;
	
	public Vector getNewHyp() {
		return newHyp;
	}

	/**
	 * Proves the obvious goals if asked.
	 * Cast all the remaining lemmas in {@link SimpleLemma} if asked.
	 * @param prove indicate whether obvious goals should be suppressed from 
	 * the theorems
	 * @param atTheEnd indicate whether lemmas should be casted in simple lemma
	 **/
	TheoremList proveObvious(boolean prove, boolean atTheEnd) {
		 Theorem tmp = th.proveObvious(prove, atTheEnd);
		newHyp = th.getNewHyp();
		if (tmp.nbLemmas() == 0)
			 if (next == null)
				 return null;
			 else {
			return next.proveObvious(prove, atTheEnd);
			 }
		else {
			th = tmp;
			if (next != null) {
				next = next.proveObvious(prove, atTheEnd);
				if (next != null)
				newHyp.addAll(next.getNewHyp());
			}
			return this;
		}
	}

	/**
	 * Selects in the lemmas corresponding to behaviours, the cases 
	 * corresponding to labels.
	 * @param labels set of labels that have to be selected
	 * @throws WrongLabelException if a behaviour does not contain any 
	 * remaining case after the selection.
	 */
	void selectLabel(Vector labels) throws WrongLabelException {
		th.selectLabel(labels);
		if (next != null)
			next.selectLabel(labels);
	}

	/**
	 * Collects all the exception type that are declared in the exsures lemmas 
	 * of the theorems of the list.
	 * @param s set of {@link jml2b.structure.java.Type}
	 * @throws jml2b.exceptions.InternalError when the method is called with a
	 * theorem list containing {@link NormalLemma} or a {@link SimpleLemma}. 
	 **/
	void getTypesException(Set s) {
		th.getTypesException(s);
		if (next != null)
			next.getTypesException(s);

	}

	/**
	 * Calculate the theorem list resulting from the throw of an exception .
	 * @param vv Instance of the thrown exception.
	 * @param c  Formula containing the class of the thrown exception.
	 */
	TheoremList throwException(Formula vv, Formula c, Vector subs) {
		return new TheoremList(
			th.throwException(vv, c, subs),
			next == null ? null : next.throwException(vv, c, subs));
	}

	/**
	 * Calculate the theorem list resulting from the throw of an exception .
	 * @param vv Instance of the thrown exception.
	 * @param c  Formula containing the class of the thrown exception.
	 */
	TheoremList throwException(String vv, AClass c, Vector subs) {
		return new TheoremList(
			th.throwException(vv, c, subs),
			next == null ? null : next.throwException(vv, c, subs));
	}

	/**
	 * Constructs a new list of theorems resulting from the old list catching an 
	 * exception
	 * @param type The catched exception
	 * @param catchParam The catched exception parameter
	 **/
	TheoremList catchException(Type type, Field catchParam) {
		th.catchException(type, catchParam);
		if (next != null)
			next.catchException(type, catchParam);
		return this;
	}

	/**
	 * Returns whether a exsures lemma of a theorem of the list catches a given 
	 * exception.
	 * @param c The class of the tested exception
	 * @return <code>true</code> if an exsures lemma of a theorem of the list 
	 * contains an exception type that is a super type of the given class, 
	 * <code>false</code> otherwise
	 */
	boolean catches(AClass c) {
		if (th.catches(c))
			return true;
		else if (next == null)
			return false;
		else
			return next.catches(c);
	}

	Vector getHyp() {
		Vector res = th.getHyp();
		if (next != null) {
			res.addAll(next.getHyp());
		}
		return res;

	}

	public void getFields(Set fields) {
		th.getFields(fields);
		if (next != null)
			next.getFields(fields);
	}

	/**
	 * Add a new node in the case name of all theorems.
	 * @param i The name, it can be 1 or 2.
	 **/
	void addCase(int i) {
		th.addCase(i);
		if (next != null)
			next.addCase(i);
	}

}