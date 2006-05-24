//******************************************************************************
/* Copyright (c) 2002, 2003 GEMPLUS Software Research Labs. All Rights Reserved.
/* Copyright (c) 2003, 2004 INRIA. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: Theorem.java
/*
/*******************************************************************************
/* Warnings/Remarks:
/*  09/26/2003 : Simplify integration achieved
/******************************************************************************/
package jml2b.pog.lemma;

import java.io.IOException;
import java.util.Enumeration;
import java.util.Set;
import java.util.Vector;

import jml.JmlDeclParserTokenTypes;
import jml2b.IJml2bConfiguration;
import jml2b.exceptions.Jml2bException;
import jml2b.exceptions.PogException;
import jml2b.exceptions.WrongLabelException;
import jml2b.formula.BinaryForm;
import jml2b.formula.Formula;
import jml2b.formula.IFormToken;
import jml2b.formula.TerminalForm;
import jml2b.formula.UnaryForm;
import jml2b.pog.substitution.SubForm;
import jml2b.pog.substitution.Substitution;
import jml2b.pog.util.ColoredInfo;
import jml2b.structure.IAParameters;
import jml2b.structure.java.AClass;
import jml2b.structure.java.Field;
import jml2b.structure.java.Identifier;
import jml2b.structure.java.JmlFile;
import jml2b.structure.java.Method;
import jml2b.structure.java.Parameters;
import jml2b.structure.java.Type;
import jml2b.structure.jml.Exsures;
import jml2b.structure.statement.Expression;
import jml2b.structure.statement.MyToken;
import jml2b.util.JpoOutputStream;
import jml2b.util.Profiler;

/**
 * This class describes a theorem.
 * A theorem is a set of hypothesis and a set of lemmas corresponding to goals.
 * 
 * @author L. Burdy
 **/
public class Theorem
	extends Profiler
	implements JmlDeclParserTokenTypes, MyToken, IFormToken {

	public static Theorem getTrue(IJml2bConfiguration config)
		throws PogException, Jml2bException {
		return new Theorem(
			new SimpleLemma(
				config,
				Expression.getTrue(),
				new GoalOrigin(GoalOrigin.STATIC_INVARIANT)));
	}

	/**
	 * Returns whether a formula belongs to a set of formula.
	 * @param f1 checked formula
	 * @param h2 list of formula
	 * @return <code>true</code> if the formula equals to a formula of the set,
	 * <code>false</code> otherwise
	 * @see Formula#equals(Object)
	 **/
	private static boolean isExactlyIn(Formula f1, Vector h2) {
		Enumeration e = h2.elements();
		while (e.hasMoreElements()) {
			Formula f2 = ((VirtualFormula) e.nextElement()).getFormula();
			if (f2.equals(f1))
				return true;
		}
		return false;
	}

	/**
	 * Returns whether a formula belongs to a set of formula.
	 * Used during the merging phase.
	 * @param f1 checked loaded formula
	 * @param h2 list of formula
	 * @return <code>true</code> if the formula equals to a formula of the set,
	 * <code>false</code> otherwise
	 * @see Formula#is(Formula)
	 **/
	private static boolean isIn(Formula f1, Vector h2) {
		Enumeration e = h2.elements();
		while (e.hasMoreElements()) {
			Formula f2 = ((VirtualFormula) e.nextElement()).getFormula();
			if (f2.is(f1))
				return true;
		}
		return false;
	}

	/**
	 * Returns whether a set of formula is a subset of another set of formula.
	 * Used during the merging phase.
	 * @param h1 list of loaded formula
	 * @param h2 list of formula
	 * @return <code>true</code> if the first formula set contains only
	 * formulas that belongs to the second set, <code>false</code> otherwise
	 * @see Theorem#isIn(Formula,Vector)
	 **/
	private static boolean isSubset(jpov.structure.VirtualFormula[] h1, Vector h2) {
		for (int i=0; i < h1.length; i++) {
			Formula f = h1[i].getF();
			if (!f.isObvious(true) && isNotSubFormula(f, h2))
				return false;
		}
		return true;
	}
	
	private static boolean isNotSubFormula(Formula f, Vector h2) {
		if (f.getNodeType() == IFormToken.Ja_AND_OP) {
			return isNotSubFormula(((BinaryForm) f).getLeft(), h2) ||
			isNotSubFormula(((BinaryForm) f).getRight(), h2);
		}
		else
			return !isIn(f,h2);
	}

	/**
	 * Name of the theorem, this name is usefull to write the Atelier B files.
	 **/
	private String name;

	/**
	 * Set of hypothesis. Thoses hypothesis are pointers to the hypothesis
	 * of the proof on which this theorem belongs ({@link Proofs#locHyp}).
	 **/
	private Vector hyp;

	/**
	 * Set of lemmas.
	 **/
	private Vector lemmas;

	/**
	 * Set of colored info
	 **/
	private Vector flow;

	private String caseNum = "0";

	/*@
	  @ private invariant hyp != null
	  @                && hyp.elementType <: \type(VirtualFormula)
	  @                && lemmas != null
	  @                && lemmas.elementType <: \type(LemmaViewer)
	  @                && flow != null
	  @                && flow.elementType <: \type(ColoredInfo);
	  @*/

	/**
	 * Construct an empty theorem.
	 **/
	public Theorem() {
		hyp = new Vector();
		flow = new Vector();
		lemmas = new Vector();
	}

	/**
	 * Construct a theorem from an enumeration of {@link Exsures}.
	 * A {@link ExsuresLemma} is constructed for each element of the enumeration,
	 * @param e {@link Exsures} enumeration
	 * @param b {@link Expression} to substitued to <code>this</code> in the 
	 * exsures clause (may be <code>null</code>)
	 * @param origin origin of the exsures
	 **/
	public Theorem(
		IJml2bConfiguration config,
		Enumeration e,
		Expression b,
		GoalOrigin origin)
		throws Jml2bException, PogException {
		this();
		while (e.hasMoreElements()) {
			Lemma l =
				new ExsuresLemma(
					config,
					(Exsures) e.nextElement(),
					b,
					origin);
			lemmas.add(l);
		}
	}

	/**
	 * Construct a theorem from a method specification corresponding to the 
	 * proof of its normal behaviours.
	 * @param m method from which lemmas should be created
	 * @param l The current invariant
	 * @param sc The current static constraint
	 * @param ic The current instance constraint
	 * @param fiels seen fields from this method, usefull to create the 
	 * modifies lemma 
	 **/
	public Theorem(
		IJml2bConfiguration config,
		Method m,
		SimpleLemma l,
		SimpleLemma sc,
		SimpleLemma ic,
		Vector fields)
		throws Jml2bException, PogException {
		this();
		lemmas.add(new NormalLemma(config, m, l, sc, ic, fields));
	}

	/**
	 * Construct a theorem containing one lemma
	 * @param l lemma to add to the theorem
	 **/
	public Theorem(Lemma l) {
		this();
		lemmas.add(l);
	}

	/**
	 * Clone the theorem
	 * @return the cloned theorem
	 **/
	public Object clone() {
		Theorem res = new Theorem();
		res.name = name;
		res.caseNum = caseNum;
		res.hyp = (Vector) hyp.clone();
		res.lemmas = new Vector();
		Enumeration e = lemmas.elements();
		while (e.hasMoreElements()) {
			Lemma g = (Lemma) e.nextElement();
			res.lemmas.add((Lemma) g.clone());
		}
		res.flow = (Vector) flow.clone();
		return res;
	}

	/**
	 * Returns the name of the theorem.
	 * @return the name of the theorem
	 **/
	public String getName() {
		return name;
	}

	/**
	 * Returns the hypothesis
	 * @return the enumeration of hypothesis
	 **/
	public Vector getHyp() {
		return hyp;
	}

	/**
	 * Returns the lemmas
	 * @return the enumeration of lemmas
	 **/
//	public Enumeration getLemmas() {
//		return lemmas.elements();
//	}

	/**
	 * Return the number of lemmas.
	 * @return the number of lemmas
	 **/
	int nbLemmas() {
		return lemmas.size();
	}

	/**
	 * Return a lemma
	 * @param i index of the whished lemma
	 * @return the lemma with index i
	 **/
	SimpleLemma getLemma(int i) {
		return (SimpleLemma) lemmas.elementAt(i);
	}

	/**
	 * Add a new hypothesis.
	 * If the hypothesis is <code>false</code> the hypothese is not added and
	 * all the lemmas are removed.
	 * @param f formula to add in hypothesis
	 * @return <code>true</code> if the hypothese has been added, 
	 * <code>false</code> otherwise
	 * @see Proofs#addHyp(VirtualFormula)
	 **/
	boolean addHyp(VirtualFormula f) {
		if (f.getFormula().getNodeType() == Ja_LITERAL_false) {
			lemmas = new Vector();
			return false;
		} else {
			hyp.add(f);
			return true;
		}
	}

	/**
	 * Add a new colored info.
	 * @param b colored info to add
	 * @see Proofs#addBox(ColoredInfo)
	 **/
	void addBox(ColoredInfo b) {
		flow.add(b);
	}

	/**
	 * Supress all the occurence of an hypothese and add a new one.
	 * @param vf suppressed hypothese
	 * @param newVf new hypothese
	 * @see Proofs#subHyp(VirtualFormula,VirtualFormula)
	 **/
	void subHyp(VirtualFormula vf, VirtualFormula newVf) {
		if (hyp.remove(vf)) {
			hyp.add(newVf);
			while (hyp.remove(vf));
		}
	}

	void subFlow(ColoredInfo vf, ColoredInfo newVf) {
		if (flow.remove(vf)) {
			flow.add(newVf);
			while (flow.remove(vf));
		}
	}

	/**
	 * Returns whether an hypothese belongs to the current hypothesis list.
	 * @param vf the checked hypothese
	 * @return <code>true</code> if the hypothese belongs to the list,
	 * <code>false</code> otherwise
	 * @see Proofs#isUsed(VirtualFormula)
	 **/
	boolean isUsed(VirtualFormula vf) {
		return hyp.indexOf(vf) != -1;
	}

	/**
	 * Returns the number of goals.
	 * @return the number of goals in all lemmas
	 * @see Proofs#nbPo()
	 **/
	int nbPo() {
		int res = 0;
		Enumeration e = lemmas.elements();
		while (e.hasMoreElements()) {
			Lemma l = (Lemma) e.nextElement();
			res += l.nbPo();
		}
		return res;
	}

	int nbPoChecked() {
		int res = 0;
		Enumeration e = lemmas.elements();
		while (e.hasMoreElements()) {
			Lemma l = (Lemma) e.nextElement();
			res += l.nbPoChecked();
		}
		return res;
	}

	/**
	 * Returns the number of goals that are in a specified state.
	 * @param state state of the whished goals number
	 * @return the number of goals in the lemmas list which have a state 
	 * equals to the paremeter.
	 * @see Proofs#nbProved(int)
	 **/
	int nbPoProved(String prover) {
		int res = 0;
		Enumeration e = lemmas.elements();
		while (e.hasMoreElements()) {
			Lemma g = (Lemma) e.nextElement();
			res += g.nbPoProved(prover);
		}
		return res;
	}

	/**
	 * Returns the number of goals that are in a specified state.
	 * @param state state of the whished goals number
	 * @return the number of goals in the lemmas list which have a state 
	 * equals to the paremeter.
	 * @see Proofs#nbProved(int)
	 **/
	int nbPoProved() {
		int res = 0;
		Enumeration e = lemmas.elements();
		while (e.hasMoreElements()) {
			Lemma g = (Lemma) e.nextElement();
			res += g.nbPoProved();
		}
		return res;
	}

	/**
	 * Sets the name of the theorem
	 * @param s name of the theorem
	 **/
	void setName(String s) {
		name = s;
	}

	/**
	 * Adds a <i>old</i> param around the element of the enumeration
	 * corresponding to the parameter of the method.
	 * @param e fields enumeration
	 **/
	public void oldParam(Vector e) {
		Enumeration f = lemmas.elements();
		while (f.hasMoreElements()) {
			Lemma l = (Lemma) f.nextElement();
			l.oldParam(e);
		}
	}

	/**
	 * Apply a substitution to the lemmas. Hypothesis are not directly 
	 * substituted but pointers are changed.
	 * @param s substitution to apply.
	 * @see Proofs#sub(Substitution)
	 **/
	void sub(Substitution s) {
		Enumeration e = lemmas.elements();
		while (e.hasMoreElements()) {
			Lemma goal = (Lemma) e.nextElement();
			goal.sub(s);
		}
	}

	/**
	 * Suppress the <i>Called Old</i> expressions.
	 **/
	void suppressSpecialOld(int token) {
		Enumeration e = lemmas.elements();
		while (e.hasMoreElements()) {
			Lemma goal = (Lemma) e.nextElement();
			goal.suppressSpecialOld(token);
		}
	}

	/**
	 * Saves the theorem in a 
	 * <a href="{@docRoot}/jpov/doc-files/jpo.html"> .jpo file</a>
	 * Remark that hypothesis are saved by an index in the hypothesis array of
	 * the current proof
	 * @param s output stream for the jpo file
	 * @param jf current {@link JmlFile}
	 * @see ColoredInfo#save(DataOutputStream, JmlFile)
	 * @see SimpleLemma#save(DataOutputStream, JmlFile)
	 * @see Proofs#save(DataOutputStream, JmlFile)
	 * @throws IOException
	 **/
	void save(IJml2bConfiguration config, JpoOutputStream s, JmlFile jf) throws IOException {
		s.writeUTF(name);
		s.writeUTF(caseNum);
		s.writeInt(hyp.size());
		Enumeration e = hyp.elements();
		while (e.hasMoreElements()) {
			s.writeInt(((VirtualFormula) e.nextElement()).getIndex());
		}
		s.writeInt(nbPo());
		e = lemmas.elements();
		while (e.hasMoreElements())
			 ((SimpleLemma) e.nextElement()).save(config, s, jf);
		s.writeInt(flow.size());
		e = flow.elements();
		while (e.hasMoreElements()) {
			s.writeInt(((ColoredInfo) e.nextElement()).getIndex());
		}
	}

	/**
	 * Merges the theorem with a loaded theorem.
	 * Lemmas are merged with the loaded lemmas if the current hypothesis are
	 * a subset of the hypothesis of the loaded theorem.
	 * @param t The loaded theorem
	 **/
	void mergeWith(jpov.structure.Lemma t) {
		if (isSubset(t.getHyp(), hyp)) {
			Enumeration e1 = lemmas.elements();
			while (e1.hasMoreElements())
				 ((SimpleLemma) e1.nextElement()).mergeWith(t.getGoals());
		}
	}

	/**
	 * Returns whether a contradiction is found in hypothesis.
	 * Contradiction searched are
	 * <UL>
	 * <li> a hypothese is <code>true == false</code> or 
	 *      <code>false == true</code>
	 * <li> a hypothese matches with <code>a == null</code> and another with 
	 *      <code>!a == null</code>
	 * <li> a hypothese matches with <code>a == true</code> and another with 
	 *      <code>a == false</code>
	 * <li> a hypothese matches with <code>bool(!a) == b</code> and another with 
	 *      <code>bool(a) == b</code>
	 * <li> a hypothese matches with <code>bool(a != c) == b</code> and another 
	 *      with <code>bool(a == c) == b</code>
	 * </UL>
	 * @return <code>true</code> if a contradiction is found, 
	 * <code>false</code> otherwise
	 **/
	private boolean contradictionInHyp() {
		Enumeration e = hyp.elements();
		while (e.hasMoreElements()) {
			Formula f = ((VirtualFormula) e.nextElement()).getFormula();
			if (f.isBFalse())
				return true;
			else if (
				f.matchAEqualsNull()
					&& isExactlyIn(new UnaryForm(Ja_LNOT, f), hyp))
				return true;
			else if (
				f.getNodeType() == Ja_EQUALS_OP
					&& ((BinaryForm) f).getRight().getNodeType()
						== Ja_LITERAL_true
					&& isExactlyIn(
						new BinaryForm(
							Ja_EQUALS_OP,
							((BinaryForm) f).getLeft(),
							new TerminalForm(Ja_LITERAL_false)),
						hyp))
				return true;
			else if (
				f.getNodeType() == Ja_EQUALS_OP
					&& ((BinaryForm) f).getLeft().getNodeType() == B_BOOL
					&& ((UnaryForm) ((BinaryForm) f).getLeft())
						.getExp()
						.getNodeType()
						== Ja_LNOT
					&& isExactlyIn(
						new BinaryForm(
							Ja_EQUALS_OP,
							new UnaryForm(
								B_BOOL,
								((UnaryForm) ((UnaryForm) ((BinaryForm) f)
									.getLeft())
									.getExp())
									.getExp()),
							((BinaryForm) f).getRight()),
						hyp))
				return true;
			else if (
				f.getNodeType() == Ja_EQUALS_OP
					&& ((BinaryForm) f).getLeft().getNodeType() == B_BOOL
					&& ((UnaryForm) ((BinaryForm) f).getLeft())
						.getExp()
						.getNodeType()
						== Ja_DIFFERENT_OP
					&& isExactlyIn(
						new BinaryForm(
							Ja_EQUALS_OP,
							new UnaryForm(
								B_BOOL,
								new BinaryForm(
									Ja_EQUALS_OP,
									((BinaryForm) ((UnaryForm) ((BinaryForm) f)
										.getLeft())
										.getExp())
										.getLeft(),
									((BinaryForm) ((UnaryForm) ((BinaryForm) f)
										.getLeft())
										.getExp())
										.getRight())),
							((BinaryForm) f).getRight()),
						hyp))
				return true;
		}
		return false;
	}

	Vector newHyp;
	
	
	public Vector getNewHyp() {
		return newHyp;
	}

	/**
	 * Proves the obvious goals if asked : tries to find a contradiction in 
	 * hypothesis or try to prove the lemmas.
	 * Cast all the remaining lemmas in {@link SimpleLemma} if asked.
	 * @param prove indicate whether obvious goals should be suppressed from 
	 * the theorems
	 * @param atTheEnd indicate whether lemmas should be casted in simple lemma
	 **/
	Theorem proveObvious(boolean prove, boolean atTheEnd) {
		newHyp = new Vector();
		if (prove && contradictionInHyp()) {
			lemmas = new Vector();
		} else {
			Vector newLemmas = new Vector();
			Enumeration e = lemmas.elements();
			while (e.hasMoreElements()) {
				Lemma l = (Lemma) e.nextElement();
				if (!prove || !l.proveObvious(hyp, atTheEnd)) {
					if (atTheEnd) {
						SimpleLemma sl = new SimpleLemma(l);
						newLemmas.add(sl);
						Enumeration e1 = sl.getPureMethodDefs().elements();
						while (e1.hasMoreElements()) {
							Formula f = (Formula) e1.nextElement();
							VirtualFormula vf = new VirtualFormula(VirtualFormula.PURE_METHOD_DECLARATION, f, (ColoredInfo) null);
							hyp.add(vf);
							newHyp.add(vf);
						}
					}
					else
						newLemmas.add(l);
				}
			}
			lemmas = newLemmas;
		}
		return this;
	}

	/**
	 * Annotates all the fields that appear in the theorem to declare them in 
	 * the Atelier B files.
	 **/
	void garbageIdent() {
		Enumeration e = lemmas.elements();
		while (e.hasMoreElements()) {
			Lemma element = (Lemma) e.nextElement();
			element.garbageIdent();
		}
	}

	/**
	 * Renames the parameter of a method with new identifier in the theorem
	 * @param signature The parameters of a method
	 * @param newSignature The set of new names
	 * @return the substituted theorem
	 **/
	private Theorem renameParam(
		Enumeration signature,
		Enumeration newSignature) {
		if (signature.hasMoreElements()) {
			Field f = (Field) signature.nextElement();
			TerminalForm f1 = new TerminalForm(new Identifier(f));
			Formula f2 = new TerminalForm((String) newSignature.nextElement());
			//          f2.stateType = f.getType();
			Theorem res = renameParam(signature, newSignature);
			res.sub(new SubForm(f1, f2));
			return res;
		} else
			return this;
	}

	/**
	 * Renames the parameter of a method with new identifier in the theorem
	 * @param signature The parameters of a method
	 * @param newSignature The set of new names
	 * @return the substituted theorem
	 **/
	public Theorem renameParam(IAParameters signature, Vector newSignature) {
		if (signature instanceof Parameters)
		return renameParam(
			((Parameters) signature).signature.elements(),
			newSignature.elements());
		else
			return this;
	}

	/**
	 * Selects in the lemmas corresponding to behaviours, the cases 
	 * corresponding to labels.
	 * @param labels set of labels that have to be selected
	 * @throws WrongLabelException if a behaviour does not contain any 
	 * remaining case after the selection.
	 **/
	void selectLabel(Vector labels) throws WrongLabelException {
		Enumeration e = lemmas.elements();
		while (e.hasMoreElements()) {
			Lemma element = (Lemma) e.nextElement();
			element.selectLabel(labels);
		}
	}

	/**
	 * Collects all the exception type that are declared in the exsures lemmas 
	 * of this theorem.
	 * @param s set of {@link jml2b.structure.java.Type}
	 * @throws jml2b.exceptions.InternalError when the method is called with a
	 * theorem containing {@link NormalLemma} or a {@link SimpleLemma}. 
	 **/
	void getTypesException(Set s) {
		Enumeration e = lemmas.elements();
		while (e.hasMoreElements()) {
			Lemma element = (Lemma) e.nextElement();
			element.getTypesException(s);
		}
	}

	void getFields(Set fields) {
		Enumeration e = lemmas.elements();
		while (e.hasMoreElements()) {
			Lemma element = (Lemma) e.nextElement();
			element.getFields(fields);
		}
	}

	/**
	 * Calculate the theorem resulting from the throw of an exception .
	 * @param vv Instance of the thrown exception.
	 * @param c  Formula containing the class of the thrown exception.
	 */
	Theorem throwException(Formula vv, Formula c, Vector subs) {
		Theorem res = (Theorem) clone();
		Vector tmp = new Vector();
		Enumeration e = lemmas.elements();
		while (e.hasMoreElements()) {
			Lemma element = (Lemma) e.nextElement();
			tmp.add(element.throwException(vv, c, subs));
		}
		res.lemmas = tmp;
		return res;
	}

	/**
	 * Calculate the lemmas resulting from the throw of an exception .
	 * @param vv Instance of the thrown exception.
	 * @param c  Formula containing the class of the thrown exception.
	 */
	Theorem throwException(String vv, AClass c, Vector subs) {
		Theorem res = (Theorem) clone();
		Vector tmp = new Vector();
		Enumeration e = lemmas.elements();
		while (e.hasMoreElements()) {
			Lemma element = (Lemma) e.nextElement();
			tmp.add(element.throwException(vv, c, subs));
		}
		res.lemmas = tmp;
		return res;
	}

	/**
	 * Constructs a new set of lemmas resulting from the old set catching an 
	 * exception
	 * @param type The catched exception
	 * @param catchParam The catched exception parameter
	 **/
	void catchException(Type type, Field catchParam) {
		Vector tmp = new Vector();
		Enumeration e = lemmas.elements();
		while (e.hasMoreElements()) {
			Lemma element = (Lemma) e.nextElement();
			tmp.add(element.catchException(type, catchParam));
		}
		lemmas = tmp;
	}

	/**
	 * Returns the proof that an exsures proof proof implies an exceptionnal 
	 * behaviour.
	 * @param ebs The exceptional behaviour
	 * @return the calculated proof
	 **/
	public Proofs impliesExceptional(ExceptionalBehaviourStack ebs) {
		Proofs res = new Proofs();
		Enumeration e = lemmas.elements();
		while (e.hasMoreElements()) {
			ExsuresLemma element = (ExsuresLemma) e.nextElement();
			res.addAll(element.impliesExceptional(ebs));
		}
		return res;

	}

	/**
	 * Returns whether a exsures lemma of the theorem catches a given exception.
	 * @param c The class of the tested exception
	 * @return <code>true</code> if an exsures lemma of the current theorem 
	 * contains an exception type that is a super type of the given class, 
	 * <code>false</code> otherwise
	 */
	boolean catches(AClass c) {
		Enumeration e = lemmas.elements();
		while (e.hasMoreElements()) {
			Lemma element = (Lemma) e.nextElement();
			if (element.catches(c))
				return true;
		}
		return false;
	}

	/**
	 * Add a new node in the case name
	 * @param i The name, it can be 1 or 2.
	 **/
	void addCase(int i) {
		caseNum = i + "." + caseNum;

	}

}