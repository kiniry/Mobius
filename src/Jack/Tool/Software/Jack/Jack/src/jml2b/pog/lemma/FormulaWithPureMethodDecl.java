/*
 * Created on Oct 12, 2005
 *
 * To change the template for this generated file go to
 * Window&gt;Preferences&gt;Java&gt;Code Generation&gt;Code and Comments
 */
package jml2b.pog.lemma;

import java.util.Enumeration;
import java.util.Vector;

import jml2b.exceptions.PogException;
import jml2b.formula.BinaryForm;
import jml2b.formula.Formula;
import jml2b.formula.IFormToken;
import jml2b.formula.TerminalForm;
import jml2b.formula.UnaryForm;
import jml2b.structure.IAParameters;
import jml2b.structure.java.Field;
import jml2b.structure.java.Identifier;
import jml2b.structure.java.Parameters;

public class FormulaWithPureMethodDecl {

	
	/**
	 * Returns the implicative formula between the two parameters.
	 * @param s1 left implicative formula
	 * @param s2 right implicative formula
	 * @return the formula <code>s1 ==> s2</code>
	 **/
	public static FormulaWithPureMethodDecl implies(Formula s1, FormulaWithPureMethodDecl s2) {
		return new FormulaWithPureMethodDecl(s2, new BinaryForm(IFormToken.Jm_IMPLICATION_OP, s1, s2.getFormula()));
	}
	
	/**
	 * Returns the implicative formula between the two parameters.
	 * @param s1 left implicative formula
	 * @param s2 right implicative formula
	 * @return the formula <code>s1 ==> s2</code>
	 **/
	public static FormulaWithPureMethodDecl and(FormulaWithPureMethodDecl s1, FormulaWithPureMethodDecl s2) {
		return new FormulaWithPureMethodDecl(s1, s2, new BinaryForm(IFormToken.Ja_AND_OP, s1.getFormula(), s2.getFormula()));
	}

	public static FormulaWithPureMethodDecl or(FormulaWithPureMethodDecl s1, FormulaWithPureMethodDecl s2) {
		return new FormulaWithPureMethodDecl(s1, s2, new BinaryForm(IFormToken.Ja_OR_OP, s1.getFormula(), s2.getFormula()));
	}

	public static FormulaWithPureMethodDecl not(FormulaWithPureMethodDecl s1) {
		return new FormulaWithPureMethodDecl(s1, new UnaryForm(IFormToken.Ja_LNOT, s1.getFormula()));
	}
/**
	 * The set of pure method call definition.
	 **/
	private Vector pureMethodDefs;

	/**
	 * The result of the translation
	 **/
	private Formula f;

	/*@
	  @ private invariant results != null;
	  @               &&  results.elemtype == \type(Formula);
	  @*/

	
	public FormulaWithPureMethodDecl(Vector v, Formula f) {
		this.pureMethodDefs = v;
		this.f = f;
	}
	
	/**
	 * Constructs a context form a formula, the context is empty.
	 * @param f formula resulting form the translation of an expression without 
	 * method call or from a expression that is a predicate.
	 **/
	public FormulaWithPureMethodDecl(Formula f) {
		this.f = f;
		pureMethodDefs = new Vector();
	}

	/** Constructs a context from an existing context and a formula.
	 * @param c context that is taken into account, except its formula.
	 * @param f formula resulting form the translation of an expression without 
	 * method call or from a expression that is a predicate.
	 **/
	public FormulaWithPureMethodDecl(FormulaWithPureMethodDecl c, Formula f) {
		this(f);
		pureMethodDefs = c.pureMethodDefs;
	}

	public FormulaWithPureMethodDecl(FormulaWithPureMethodDecl c, Formula call, Formula decl) {
		this(c, call);
		pureMethodDefs.add(decl);
	}

	public FormulaWithPureMethodDecl(FormulaWithPureMethodDecl c1,
			FormulaWithPureMethodDecl c2, Formula call, Formula decl) {
		this(c1, call);
		pureMethodDefs.addAll(c2.pureMethodDefs);
		pureMethodDefs.add(decl);
	}
	
	public FormulaWithPureMethodDecl(FormulaWithPureMethodDecl c1,
			FormulaWithPureMethodDecl c2, FormulaWithPureMethodDecl c3, Formula call, Formula decl) {
		this(c1, call);
		pureMethodDefs.addAll(c2.pureMethodDefs);
		pureMethodDefs.addAll(c3.pureMethodDefs);
		pureMethodDefs.add(decl);
	}
	
//	/**
//	 * Constructs a context from a method call without parameter.
//	 * @param res the field corresponding to the result of the call
//	 * @param t the returned type of the method called
//	 * @param ens the ensures clause of the method called
//	 **/
//	public FormulaWithPureMethodDecl(String f, Formula res, Type t, Formula ens) {
//		this(res);
//		results.add(new TemporaryField(t, t, f));
//		ensures = ens;
//	}

//	/**
//	 * Constructs a context from a method call with parameter.
//	 * @param c context issued from the translation of the parameters.
//	 * @param res the field corresponding to the result of the call
//	 * @param t the returned type of the method called
//	 * @param ens the ensures clause of the method called
//	 **/
//	public ContextFromPureMethod(
//		ContextFromPureMethod c,
//		String res,
//		Formula f,
//		Type t,
//		Formula ens) {
//		this(f);
//		if (c.results.size() == 0) {
//			ensures = ens;
//		} else {
//			results = c.results;
//			ensures = new BinaryForm(Ja_AND_OP, c.ensures, ens);
//		}
//		results.add(new TemporaryField(t, t, res));
//	}

	/**
	 * Constructs a context from the translation of a binary operator.
	 * @param c1 context issued form the translation of one part.
	 * @param c2 context issued form the translation of the other part.
	 * @param f translation resulting formula
	 **/
	public FormulaWithPureMethodDecl(
			FormulaWithPureMethodDecl c1,
			FormulaWithPureMethodDecl c2,
		Formula f) {
		this(f);
		pureMethodDefs.addAll(c1.pureMethodDefs);
		pureMethodDefs.addAll(c2.pureMethodDefs);
	}

	/**
	 * Constructs a context from the translation of a 3-ary operator.
	 * @param c1 context issued form the translation of a part.
	 * @param c2 context issued form the translation of another part.
	 * @param c3 context issued form the translation of another part.
	 * @param f translation resulting formula
	 **/
	public FormulaWithPureMethodDecl(
			FormulaWithPureMethodDecl c1,
			FormulaWithPureMethodDecl c2,
			FormulaWithPureMethodDecl c3,
		Formula f) {
		this(c1, c2, f);
		pureMethodDefs.addAll(c3.pureMethodDefs);
	}

	public Object clone() {
		Vector tmp = new Vector();
		Enumeration e = pureMethodDefs.elements();
		while (e.hasMoreElements()) {
			Formula element = (Formula) e.nextElement();
			tmp.add(element.clone());
		}
		return new FormulaWithPureMethodDecl(tmp, (Formula) getFormula().clone());
	}
	/**
	 * Returns the result of the translation.
	 * @return the formula quantified by the contextual part.
	 **/
	public Vector getPureMethodDef() {
		return pureMethodDefs;
	}

	/**
	 * Returns the formula.
	 * @return the formula without its context.
	 **/
	public Formula getFormula() {
		return f;
	}

	public void old() {
	Vector res = new Vector();
	Enumeration e = getPureMethodDef().elements();
	while (e.hasMoreElements()) {
		Formula element = (Formula) e.nextElement();
		res.add(new UnaryForm(IFormToken.Jm_T_OLD, element));
	}
	pureMethodDefs = res;
	}
	
	public void processIdent() {
		f.processIdent();
		Enumeration e = pureMethodDefs.elements();
		while (e.hasMoreElements()) {
			Formula element = (Formula) e.nextElement();
			element.processIdent();
		}
	}
	
	public FormulaWithPureMethodDecl sub(Formula a, Formula b, boolean subInCalledOld) {
		Formula tmpf, f  = getFormula().sub(a,b,subInCalledOld);
		boolean changed = f != getFormula();
		Vector tmp = new Vector();
		Enumeration e = pureMethodDefs.elements();
		while (e.hasMoreElements()) {
			Formula element = (Formula) e.nextElement();
			tmpf = element.sub(a,b,subInCalledOld);
			changed = changed || tmpf != element;
			tmp.add(tmpf);
		}
		if (changed)
		return new FormulaWithPureMethodDecl(tmp,f);
		else
			return this;
	}

	public FormulaWithPureMethodDecl sub(Field a, Field b, boolean subInCalledOld) {
		Formula f1 = new TerminalForm(new Identifier(a));
		Formula f2 = new TerminalForm(new Identifier(b));
		return sub(f1, f2, subInCalledOld);

	}

	public FormulaWithPureMethodDecl instancie(Formula  b) {
		f.instancie(b);
		Enumeration e = pureMethodDefs.elements();
		while (e.hasMoreElements()) {
			Formula element = (Formula) e.nextElement();
			element.instancie(b);
		}
		return this;
	}

	private FormulaWithPureMethodDecl renameParam(
			Enumeration signature,
			Enumeration newSignature) {
			if (signature.hasMoreElements()) {
				Field f = (Field) signature.nextElement();
				TerminalForm f1 = new TerminalForm(new Identifier(f));
				Object o = newSignature.nextElement();
				Formula f2;
				if (o instanceof String)
					f2 = new TerminalForm((String) o);
				else
					f2 = (Formula) o;
				return renameParam(signature, newSignature).sub(f1, f2, true);
			} else
				return (FormulaWithPureMethodDecl) clone();
		}

	public FormulaWithPureMethodDecl renameParam(IAParameters signature, Vector newSignature)
	throws PogException {
	if (signature instanceof Parameters)
	return renameParam(
		((Parameters) signature).signature.elements(),
		newSignature.elements());
	else
		return this;
}

}
