//******************************************************************************
/* Copyright (c) 2002, 2003 GEMPLUS Software Research Labs. All Rights Reserved.
 /* Copyright (c) 2003, 2004 INRIA. All Rights Reserved.
 /*------------------------------------------------------------------------------
 /* Name: Proofs.java
 /*
 /*******************************************************************************
 /* Warnings/Remarks:
 /*  09/26/2003 : Simplify integration achieved
 /******************************************************************************/
package jml2b.pog.lemma;

import java.io.IOException;
import java.io.Serializable;
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
import jml2b.formula.TTypeForm;
import jml2b.formula.TerminalForm;
import jml2b.formula.UnaryForm;
import jml2b.pog.substitution.SubForm;
import jml2b.pog.substitution.SubTmpVar;
import jml2b.pog.substitution.Substitution;
import jml2b.pog.util.ColoredInfo;
import jml2b.structure.IAParameters;
import jml2b.structure.java.Field;
import jml2b.structure.java.Identifier;
import jml2b.structure.java.JmlFile;
import jml2b.structure.java.Parameters;
import jml2b.structure.java.Type;
import jml2b.structure.statement.BinaryExp;
import jml2b.structure.statement.Expression;
import jml2b.structure.statement.Statement;
import jml2b.util.JpoOutputStream;

/**
 * This class describes all the proof obligations associated with a method or
 * with the static initialisation. It is the result of the weakest precondition
 * calculus. It contains a list of hypothesis and a list of theorem.
 * 
 * @author L. Burdy
 */
public class Proofs implements JmlDeclParserTokenTypes, Serializable, IFormToken {

	/**
	 * The set of hypothesis that are pointed by the theorems. The vector
	 * handles {@link VirtualFormula}.
	 */
	protected Vector locHyp;

	protected Vector locFlow;
	
//	/**
//	 * The set of pure method declarations used in this theorem.The vector
//	 * handles {@link VirtualFormula}.
//	 */
//	protected Vector declPureMeth;

	/**
	 * The list of theorem. It may be null.
	 */
	protected TheoremList thl;

	/*
	 * @ @ protected invariant locHyp != null; @ && locHyp.elementType <:
	 * \type(VirtualFormula); @
	 */

	/**
	 * Construct an empty proof.
	 */
	public Proofs() {
		locHyp = new Vector();
		locFlow = new Vector();
	}

	/**
	 * Construct a proof from a lemma
	 */
	public Proofs(jml2b.pog.lemma.Lemma l) {
		this();
		thl = new TheoremList(l);
	}

	/**
	 * Construct a proof from a theorem
	 */
	public Proofs(Theorem t) {
		this();
		thl = new TheoremList(t);
	}

	/**
	 * Clones a proof.
	 * 
	 * @return the cloned proof
	 */
	public Object clone() {
		Proofs res = new Proofs();
		Enumeration e = locHyp.elements();
		while (e.hasMoreElements()) {
			VirtualFormula vf = (VirtualFormula) e.nextElement();
			res.locHyp.add(vf);
		}
		e = locFlow.elements();
		while (e.hasMoreElements()) {
			ColoredInfo vf = (ColoredInfo) e.nextElement();
			res.locFlow.add(vf);
		}
		while (e.hasMoreElements()) {
			ColoredInfo vf = (ColoredInfo) e.nextElement();
			res.locFlow.add(vf);
		}
		res.thl = thl == null ? null : (TheoremList) thl.clone();
		return res;
	}

	/**
	 * Returns the list of theorems.
	 */
	public TheoremList getThl() {
		return thl;
	}

	/**
	 * Returns the hypothesis
	 */
	public Enumeration getLocHyp() {
		return locHyp.elements();
	}

	/**
	 * Finalize the proof obligations by
	 * <UL>
	 * <li> adding the parameters typing in hypothesis
	 * <li> adding the invariant coming from the final static field
	 * initialization in hypothesis
	 * <li> adding the invariant in hypothesis
	 * <li> adding the requires of the current method in hypothesis
	 * <li> assigning a name
	 * </UL>
	 * 
	 * @param param
	 *            the Formula corresponding to parameters declaration (may be
	 *            null)
	 * @param invStaticFinalFields
	 *            the Expression corresponding to the final static fields
	 *            initialization (may be null)
	 * @param hyp
	 *            the Formula corresponding to the invariant (may be null)
	 * @param rep
	 *            the Formula corresponding to the requires clause
	 * @param name
	 *            prefix for the PO of this proof (used to generate the Atelier
	 *            B files)
	 * @param b
	 *            the ColoredInfo associated to the requires clause.
	 */
	public void finalize(IJml2bConfiguration config, Formula param, Expression invStaticFinalFields,
			FormulaWithSpecMethodDecl hyp, FormulaWithSpecMethodDecl req, String name, ColoredInfo b, ColoredInfo method)
			throws Jml2bException, PogException {
		if (param != null)
			addHyp(param);
		if (invStaticFinalFields != null)
			addOneHyp(invStaticFinalFields.predToForm(config), VirtualFormula.STATIC_FINAL_FIELDS_INVARIANT);
//		if (pureMethodDecl != null)
//			addOneHyp(pureMethodDecl, VirtualFormula.PURE_METHOD_DECLARATION);
		if (hyp != null)
			addOneHyp(hyp, VirtualFormula.INVARIANT);
		if (req != null)
			addHyp(req, b, VirtualFormula.REQUIRES);
		if (thl != null)
			thl.setName(name);
		addBox(method);
	}

	/**
	 * Apply a substitution to the content of the proof. the substitution is
	 * applied on the hypothesis and on the theorems.
	 * 
	 * @param s
	 *            substitution to apply.
	 * @return the current proof substituted.
	 */
	public Proofs sub(Substitution s) {
		if (thl != null)
			thl.sub(s);
		Enumeration e = locHyp.elements();
		Vector tmp_add = new Vector();
		Vector tmp_rem = new Vector();
		while (e.hasMoreElements()) {
			VirtualFormula vf = (VirtualFormula) e.nextElement();
			VirtualFormula newVf = vf.sub(s);
			if (vf != newVf) {
				tmp_add.add(newVf);
				tmp_rem.add(vf);
				subHyp(vf, newVf);
			}
		}
		locHyp.addAll(tmp_add);
		locHyp.removeAll(tmp_rem);

		return this;
	}

	/**
	 * Suppress the <i>Called Old</i> expressions in the proof.
	 * 
	 * @return the current proof when the <i>Called Old</i> have been
	 *         suppressed.
	 */
	public Proofs suppressSpecialOld(int token) {
		if (thl != null)
			thl.suppressSpecialOld(token);
		Enumeration e = locHyp.elements();
		Vector tmp_add = new Vector();
		Vector tmp_rem = new Vector();
		while (e.hasMoreElements()) {
			VirtualFormula vf = (VirtualFormula) e.nextElement();
			VirtualFormula newVf = vf.suppressSpecialOld(token);
			if (vf != newVf) {
				tmp_add.add(newVf);
				tmp_rem.add(vf);
				subHyp(vf, newVf);
			}
		}
		locHyp.addAll(tmp_add);
		locHyp.removeAll(tmp_rem);

		return this;
	}

	/**
	 * Rename the fields belonging to the signature with new names.
	 * 
	 * @param signature
	 *            the list of parameters
	 * @param a
	 *            list of names to be used to rename parameters
	 * @return the current proof renamed.
	 * @see Proofs#renameParam(Parameters,Vector)
	 */
	private Proofs renameParam(Enumeration signature, Enumeration newSignature) {
		if (signature.hasMoreElements()) {
			Field f = (Field) signature.nextElement();
			TerminalForm f1 = new TerminalForm(new Identifier(f));
			Formula f2 = new TerminalForm((String) newSignature.nextElement());
			// f2.stateType = f.getType();
			return renameParam(signature, newSignature).sub(new SubForm(f1, f2));
		} else
			return this;
	}

	/**
	 * Rename the fields belonging to the parameter list with new names. When
	 * calling a method, its formal parameter should be renamed in the
	 * specification of this method before to be substitued with the calling
	 * parameter (via a WP calculus on parameters) in manner to avoid conflits
	 * with current names. In the example below, the parameter <code>a</code>
	 * of the method <code>m2</code> is renamed when the call is performed in
	 * manner to avoid to replace <code>a</code> with <code>1</code> in all
	 * the proof.
	 * 
	 * <pre>
	 *  //@ ensures \result == 1;
	 *  int m1() {
	 *     int a = 0;
	 *     m2(1);
	 *     return a++;
	 *  }
	 *  //@ requires a == 0;
	 *  int m2(int a) {
	 *     ...
	 *  }
	 * </pre>
	 * 
	 * @param signature
	 *            the signature of the called method
	 * @param newSignature
	 *            the list of new names
	 * @return the current proof renamed
	 */
	public Proofs renameParam(IAParameters signature, Vector newSignature) {
		if (signature instanceof Parameters)
			return renameParam(((Parameters) signature).signature.elements(), newSignature.elements());
		else
			return this;
	}

	/**
	 * Renames the formal parameter of a called method by the calling
	 * parameters.
	 * 
	 * @param form
	 *            set of formal parameters
	 * @param param
	 *            expression corresponding to the calling parameters
	 * @param exceptionalBehaviour
	 *            exceptional behaviours to prove if the parameter evaluation
	 *            throws an exception
	 * @see Proofs#param(IJml2bConfiguration,Vector,Expression,ExceptionalBehaviourStack)
	 */
	private Proofs param(IJml2bConfiguration config, Enumeration form, Expression param,
			ExceptionalBehaviourStack exceptionalBehaviour) throws Jml2bException, PogException {
		if (form.hasMoreElements()) {
			String vv = Statement.fresh();
			String f1 = (String) form.nextElement();
			if (param.isComma()) {
				return ((BinaryExp) param).getLeft().wp(config,
														vv,
														param(	config,
																form,
																((BinaryExp) param).getRight(),
																exceptionalBehaviour).sub(new SubTmpVar(f1,
																new TerminalForm(vv))),
														exceptionalBehaviour);
			} else {
				Proofs p = param.wp(config, vv, sub(new SubTmpVar(f1, new TerminalForm(vv))), exceptionalBehaviour);
				return p;
			}
		} else
			return this;
	}

	/**
	 * Renames the formal parameter of a called method by the calling
	 * parameters. Calling parameters are evaluated (through the WP calculus)
	 * and the result of this evaluation is substituted to the formal parameter.
	 * 
	 * @param signature
	 *            signature of the current method.
	 * @param param
	 *            expression corresponding to the calling parameters (may be
	 *            null)
	 * @param exceptionalBehaviour
	 *            exceptional behaviours to prove if the parameter evaluation
	 *            throws an exception
	 * @return the current proof renamed.
	 */
	public Proofs param(IJml2bConfiguration config, Vector signature, Expression param,
			ExceptionalBehaviourStack exceptionalBehaviour) throws Jml2bException, PogException {
		if (param == null)
			return this;
		else {
			Proofs p = param(config, signature.elements(), param.normComma(null), exceptionalBehaviour);
			return p;
		}
	}

	/**
	 * Quantifies the proof whith a variable.
	 * 
	 * @param var
	 *            the quantified variable
	 * @param type
	 *            the type of the quantified variable
	 * @param b
	 *            {@link ColoredInfo} associated to the added hypothesis
	 * @return the current proof with a new hypothesis corresponding to the
	 *         variable declation
	 */
	public Proofs quantify(String var, Type type, ColoredInfo b) {
		if (type.isBuiltin())
			addHyp(	new BinaryForm(LOCAL_VAR_DECL, new TerminalForm(var), new TTypeForm(IFormToken.T_TYPE, type)),
					b,
					VirtualFormula.ENSURES);
		else {
			addHyp(	new BinaryForm(LOCAL_VAR_DECL, new TerminalForm(var), TerminalForm.$References),
					b,
					VirtualFormula.ENSURES);
			addHyp(new BinaryForm(B_IN, new TerminalForm(var), new BinaryForm(B_UNION, TerminalForm.$instances,
					new UnaryForm(B_ACCOLADE, new TerminalForm(Ja_LITERAL_null, "null")))), b, VirtualFormula.ENSURES);
			addHyp(new BinaryForm(Jm_IMPLICATION_OP, new BinaryForm(Ja_DIFFERENT_OP, new TerminalForm(var),
					new TerminalForm(Ja_LITERAL_null, "null")), new BinaryForm(Jm_IS_SUBTYPE, new BinaryForm(
					B_APPLICATION, TerminalForm.$typeof, new TerminalForm(var)), new TTypeForm(IFormToken.Jm_T_TYPE,
					type))), b, VirtualFormula.ENSURES);
		}
		return this;
	}

	/**
	 * Quantifies the proof whith a variable.
	 * 
	 * @param var
	 *            the quantified variable
	 * @param type
	 *            the type of the quantified variable
	 * @return the current proof with a new hypothesis corresponding to the
	 *         variable declation
	 */
	public Proofs quantify(String var, Formula type) {
		return quantify(var, type, new ColoredInfo());
	}

	/**
	 * Quantifies the proof whith a variable.
	 * 
	 * @param var
	 *            the quantified variable
	 * @param type
	 *            the type of the quantified variable
	 * @param b
	 *            {@link ColoredInfo} associated to the added hypothesis
	 * @return the current proof with a new hypothesis corresponding to the
	 *         variable declation
	 */
	public Proofs quantify(String var, Formula type, ColoredInfo b) {
		addHyp(new BinaryForm(LOCAL_VAR_DECL, new TerminalForm(var), type), b, VirtualFormula.LOCALES);
		return this;
	}

	public Proofs quantify(Formula var, Formula type) {
		return quantify(var, type, new ColoredInfo());
	}

	/**
	 * Quantifies the proof whith a variable.
	 * 
	 * @param var
	 *            the quantified variable
	 * @param type
	 *            the type of the quantified variable
	 * @param b
	 *            {@link ColoredInfo} associated to the added hypothesis
	 * @return the current proof with a new hypothesis corresponding to the
	 *         variable declation
	 */
	public Proofs quantify(Formula var, Formula type, ColoredInfo b) {
		addHyp(new BinaryForm(LOCAL_VAR_DECL, var, type), b, VirtualFormula.LOCALES);
		return this;
	}

	/**
	 * Adds the goals of a lemme to the hypothesis.
	 * 
	 * @param sl
	 *            Lemme that contains the goals that are added in hypothesis
	 * @param origin
	 *            Origin of the new hypothesis
	 */
	public void addHyp(SimpleLemma sl, byte origin) {
		Enumeration e1 = sl.getGoals();
		while (e1.hasMoreElements()) {
			Goal g = (Goal) e1.nextElement();
			VirtualFormula vf = g.getVirtualFormula();
			vf.setOrigin(origin);
			addHyp(vf);
			Enumeration e = g.getPureMethodDecl().elements();
			while (e.hasMoreElements()) {
				Formula element = (Formula) e.nextElement();
				addHyp(element, (ColoredInfo) null, origin);
			}
		}
	}

	/**
	 * Adds a new hypothese.
	 * 
	 * @param vf
	 *            hypothese to add
	 */
	private void addHyp(VirtualFormula vf) {
		if (thl != null && thl.addHyp(vf))
			locHyp.add(vf);
	}

	/**
	 * Adds new hypothesis.
	 * 
	 * @param f
	 *            {@link Formula} added in hypothese. When the formula is a
	 *            conjonction, each conjective formula is added separetly
	 * @param b
	 *            {@link ColoredInfo} associated to the added hypothesis
	 * @param origin
	 *            Origin of the new hypothesis
	 */
	public void addHyp(Formula f, ColoredInfo b, byte origin) {
		if (f instanceof BinaryForm) {
			if (f.getNodeType() == IFormToken.Ja_AND_OP) {
				addHyp(((BinaryForm) f).getLeft(), b, origin);
				addHyp(((BinaryForm) f).getRight(), b, origin);
			} else if (f.getNodeType() == IFormToken.Ja_EQUALS_OP
						&& ((BinaryForm) f).getLeft().getNodeType() == IFormToken.Ja_LITERAL_true
						&& ((BinaryForm) f).getRight().getNodeType() == IFormToken.Ja_LITERAL_true) {
				addBox(b);
				return;
			} else
				addHyp(new VirtualFormula(origin, f, b));
		} else if (f.getNodeType() == IFormToken.B_BTRUE) {
			addBox(b);
			return;
		} else
			addHyp(new VirtualFormula(origin, f, b));
	}
	
	public void addHyp(FormulaWithSpecMethodDecl f, ColoredInfo b, byte origin) {
		addHyp(f.getFormula(),b,origin);
		Enumeration e = f.getPureMethodDef().elements();
		while (e.hasMoreElements()) {
			Formula element = (Formula) e.nextElement();
			addHyp(element, b, origin);
		}
	}

	/**
	 * Adds new hypothesis.
	 * 
	 * @param f
	 *            {@link Formula} added in hypothese. When the formula is a
	 *            conjonction, each conjective formula is added separetly
	 * @param b
	 *            {@link ColoredInfo} associated to the added hypothesis
	 * @param origin
	 *            Origin of the new hypothesis
	 */
	public void addHyp(Formula f, Vector b, byte origin) {
		if (f instanceof BinaryForm) {
			if (f.getNodeType() == IFormToken.Ja_AND_OP) {
				addHyp(((BinaryForm) f).getLeft(), b, origin);
				addHyp(((BinaryForm) f).getRight(), b, origin);
			} else if (f.getNodeType() == IFormToken.Ja_EQUALS_OP
						&& ((BinaryForm) f).getLeft().getNodeType() == IFormToken.Ja_LITERAL_true
						&& ((BinaryForm) f).getRight().getNodeType() == IFormToken.Ja_LITERAL_true)
				return;
			else if (f.getNodeType() == IFormToken.B_BTRUE)
				return;
			else
				addHyp(new VirtualFormula(origin, f, b));
		} else
			addHyp(new VirtualFormula(origin, f, b));
	}

	/**
	 * Adds new local hypothesis with no associated colored info.
	 * 
	 * @param f
	 *            {@link Formula} added in hypothese. When the formula is a
	 *            conjonction, each conjective formula is added separetly
	 * @param origin
	 *            Origin of the new hypothesis
	 */
	public void addHyp(Formula f) {
		addHyp(f, (ColoredInfo) null, VirtualFormula.LOCALES);
	}
	
	public void addHyp(FormulaWithSpecMethodDecl f) {
		addHyp(f, (ColoredInfo) null, VirtualFormula.LOCALES);
	}

//	/**
//	 * Adds a new hypothese.
//	 * 
//	 * @param f
//	 *            {@link Formula} added in hypothese. When the formula is a
//	 *            conjonction, a uniq formula is added.
//	 * @param b
//	 *            {@link ColoredInfo} associated to the added hypothesis
//	 * @param origin
//	 *            Origin of the new hypothesis
//	 * @see Proofs#addHyp(Formula, ColoredInfo, byte)
//	 */
//	private void addOneHyp(Formula f, byte origin) {
//		addHyp(f, (ColoredInfo) null, origin);
//		// addHyp(new VirtualFormula(origin, f, (ColoredInfo) null));
//	}

	private void addOneHyp(FormulaWithSpecMethodDecl f, byte origin) {
		addHyp(f, (ColoredInfo) null, origin);
		// addHyp(new VirtualFormula(origin, f, (ColoredInfo) null));
	}

	/**
	 * Substitue in the theorems a hypothese by another. In theorems, hypothesis
	 * are pointer to the hypothesis of {@link Proofs#locHyp}. When an
	 * hypothese is changed in {@link Proofs#locHyp}, the pointer should be
	 * changed in the theorem to point to the new hypothese.
	 * 
	 * @param vf
	 *            old hypothese
	 * @param newVf
	 *            new hypothese
	 */
	private void subHyp(VirtualFormula vf, VirtualFormula newVf) {
		if (thl != null)
			thl.subHyp(vf, newVf);
	}

	private void subFlow(ColoredInfo vf, ColoredInfo newVf) {
		if (thl != null)
			thl.subFlow(vf, newVf);
	}

	/**
	 * Concats two proofs. This means that
	 * <UL>
	 * <li> the hypothesis of the two proofs are merged without doublon
	 * <li> the theorems lists are concatened
	 * </UL>
	 * 
	 * @param l
	 *            the proof that is concatened with the current proof.
	 */
	public void addAll(Proofs l) {
		Enumeration e = l.locHyp.elements();
		while (e.hasMoreElements()) {
			VirtualFormula vf = (VirtualFormula) e.nextElement();
			int index;
			if ((index = locHyp.indexOf(vf)) != -1) {
				VirtualFormula newVf = (VirtualFormula) locHyp.get(index);
				if (vf != newVf)
					l.subHyp(vf, newVf);
			} else
				locHyp.add(vf);
		}
		e = l.locFlow.elements();
		while (e.hasMoreElements()) {
			ColoredInfo vf = (ColoredInfo) e.nextElement();
			int index;
			if ((index = locFlow.indexOf(vf)) != -1) {
				ColoredInfo newVf = (ColoredInfo) locFlow.get(index);
				if (vf != newVf)
					l.subFlow(vf, newVf);
			} else
				locFlow.add(vf);
		}
		if (thl != null) {
			if (l.getThl() != null) {
				l.getThl().addCase(1);
				thl.addCase(2);
			}
			thl.addAll(l.getThl());
		} else
			thl = l.getThl();
	}

	/**
	 * Tries to suppress obvious goals, lemmas, theorems. The suppression is
	 * performed if the parameter is <code>true</code> or if memory criteria
	 * are overpassed.
	 * 
	 * @param force
	 *            <code>true</code> if the suppression should be forced.
	 */
	public void gc(IJml2bConfiguration config, boolean force) {
		long freeMem = Runtime.getRuntime().freeMemory();
		long totalMem = Runtime.getRuntime().totalMemory();
		if (force || (totalMem > 60000000 && freeMem <= 2000000)) {
			proveObvious(true, false);
		}
	}

	/**
	 * Test wheter an hypothesis is used in the theorems.
	 * 
	 * @param vf
	 *            the tested hypothese.
	 * @return <code>true</code> if the hypothese is pointed by a theorem
	 *         <code>false</code> otherwise.
	 */
	public boolean isUsed(VirtualFormula vf) {
		return thl == null ? false : thl.isUsed(vf);
	}

	/**
	 * Returns the number of goals (or proof obligations).
	 * 
	 * @return the number of goals of the theorem list
	 */
	public int nbPo() {
		return thl == null ? 0 : thl.nbPo();
	}

	public int nbTheorems() {
		return thl == null ? 0 : thl.nbTheorems();
	}

	public int nbLemmas() {
		return thl == null ? 0 : thl.nbLemmas();
	}

	public int nbPoChecked() {
		return thl == null ? 0 : thl.nbPoChecked();
	}

	public SimpleLemma getLemma(int i) {
		return thl.getLemma(i);
	}

	public Theorem getTheorem(int i) {
		return thl.getTheorem(i);
	}

	/**
	 * Returns the number of goals that are in a specified state.
	 * 
	 * @param state
	 *            state of the whished goals number
	 * @return the number of goals of the theorem list which have a state equals
	 *         to the paremeter.
	 */
	public int nbPoProved(String prover) {
		return thl == null ? 0 : thl.nbPoProved(prover);
	}

	/**
	 * Returns the number of goals that are in a specified state.
	 * 
	 * @param state
	 *            state of the whished goals number
	 * @return the number of goals of the theorem list which have a state equals
	 *         to the paremeter.
	 */
	public int nbPoProved() {
		return thl == null ? 0 : thl.nbPoProved();
	}

	/**
	 * Adds a <i>colored info</i> to the theorems.
	 * 
	 * @param b :
	 *            added colored info
	 * @return the current proof with a new colored info
	 */
	public Proofs addBox(ColoredInfo b) {
		if (b != null) {
		if (thl != null)
			thl.addBox(b);
		locFlow.add(b);
		}
		return this;
	}

	public Vector findUsedLocHyp() {
		Vector res = new Vector();
		Enumeration e = locHyp.elements();
		while (e.hasMoreElements()) {
			VirtualFormula vf = (VirtualFormula) e.nextElement();
			if (thl.isUsed(vf))
				res.add(vf);
		}
		return res;
	}

	public Vector getLocFlow() {
		return locFlow;
	}
	/**
	 * Merge two proofs.
	 * 
	 * @param jf
	 *            proofs merged with the current one
	 * @throws MergeException
	 */
	public void mergeWith(jpov.structure.Proofs jf) {
		if (thl != null && jf.getLemmas().length != 0)
			thl.mergeWith(jf.getLemmas());
	}

	/**
	 * Proves the obvious goals if asked. Cast all the remaining lemmas in
	 * {@link SimpleLemma} if asked. This task is performed during the WP
	 * calculus in order to avoid memory overflow and at the end.
	 * 
	 * @param prove
	 *            indicate whether obvious goals should be suppressed from the
	 *            theorems
	 * @param atTheEnd
	 *            indicate whether lemmas should be casted in simple lemma
	 */
	public void proveObvious(boolean prove, boolean atTheEnd) {
		if (thl != null) {
			thl = thl.proveObvious(prove, atTheEnd);
			if (thl != null)
		locHyp.addAll(thl.getNewHyp());
	}
	}

	/**
	 * Annotates all the fields that appear in the theorem to declare them in
	 * the Atelier B files.
	 */
	public void garbageIdent() {
		Enumeration e = getLocHyp();
		while (e.hasMoreElements()) {
			VirtualFormula element = (VirtualFormula) e.nextElement();
			element.garbageIdent();
		}
		if (thl != null)
			thl.garbageIdent();
	}

	/**
	 * Selects in the lemmas corresponding to behaviours, the cases
	 * corresponding to labels.
	 * 
	 * @param labels
	 *            set of labels that have to be selected
	 * @return the current proof with some case that have be eliminated
	 * @throws WrongLabelException
	 *             if a behaviour does not contain any remaining case after the
	 *             selection.
	 */
	public Proofs selectLabel(Vector labels) throws WrongLabelException {
		if (thl != null)
			thl.selectLabel(labels);
		return this;
	}

	/**
	 * Collect the fields present in the current proof obligation.
	 * 
	 * @param fields
	 */
	public void getFields(Set fields) {
		if (thl != null)
			thl.getFields(fields);
	}

	public void saveThl(IJml2bConfiguration config, JpoOutputStream s, JmlFile jf) throws IOException {
		if (thl != null)
			thl.save(config, s, jf);
	}
	/**
	 * Saves the proof in the a <a href=" {@docRoot}/jpov/doc-files/jpo.html">
	 * .jpo file </a>
	 * 
	 * @param s
	 *            output stream for the jpo file
	 * @param jf
	 *            current {@link JmlFile}
	 * @throws IOException
	 * @see VirtualFormula#save(DataOutputStream, int, JmlFile)
	 * @see Theorem#save(DataOutputStream, JmlFile)
	 */
	public void save(IJml2bConfiguration config, JpoOutputStream s, JmlFile jf) throws IOException {
		if (nbLemmas() == 0) {
			s.writeInt(0);
			s.writeInt(0);
			s.writeInt(0);
		} else {
			int index = 0;
			Vector usedLocHyp = findUsedLocHyp();
			s.writeInt(usedLocHyp.size());
			Enumeration e = usedLocHyp.elements();
			while (e.hasMoreElements()) {
				((VirtualFormula) e.nextElement()).save(config, s, index++, jf);
			}
			s.writeInt(getLocFlow().size());
			e = getLocFlow().elements();
			index = 0;
			while (e.hasMoreElements()) {
				((ColoredInfo) e.nextElement()).save(s, index++, jf);
			}
			s.writeInt(nbTheorems());
			saveThl(config, s, jf);
		}
	}

	static final long serialVersionUID = -6703130784704083168L;

}