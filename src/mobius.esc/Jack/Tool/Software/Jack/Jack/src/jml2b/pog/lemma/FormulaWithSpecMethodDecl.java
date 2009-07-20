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
import jml2b.formula.Formula;
import jml2b.formula.IFormToken;
import jml2b.formula.TerminalForm;
import jml2b.formula.UnaryForm;
import jml2b.structure.IAParameters;
import jml2b.structure.java.Field;
import jml2b.structure.java.Identifier;
import jml2b.structure.java.Parameters;

public class FormulaWithSpecMethodDecl {

	
	/**
	 * Returns the implicative formula between the two parameters.
	 * @param s1 left implicative formula
	 * @param s2 right implicative formula
	 * @return the formula <code>s1 ==> s2</code>
	 **/
	public static FormulaWithSpecMethodDecl implies(Formula s1, FormulaWithSpecMethodDecl s2) {
		return new FormulaWithSpecMethodDecl(s2, Formula.implies(s1, s2.getFormula()));
	}
	
	/**
	 * Returns the implicative formula between the two parameters.
	 * @param s1 left implicative formula
	 * @param s2 right implicative formula
	 * @return the formula <code>s1 ==> s2</code>
	 **/
	public static FormulaWithSpecMethodDecl and(FormulaWithSpecMethodDecl s1, FormulaWithSpecMethodDecl s2) {
		return new FormulaWithSpecMethodDecl(s1, s2, Formula.and(s1.getFormula(), s2.getFormula()));
	}

	public static FormulaWithSpecMethodDecl or(FormulaWithSpecMethodDecl s1, FormulaWithSpecMethodDecl s2) {
		return new FormulaWithSpecMethodDecl(s1, s2, Formula.or(s1.getFormula(), s2.getFormula()));
	}

	public static FormulaWithSpecMethodDecl not(FormulaWithSpecMethodDecl s1) {
		return new FormulaWithSpecMethodDecl(s1, new UnaryForm(IFormToken.Ja_LNOT, s1.getFormula()));
	}
/**
	 * The set of pure method call definition.
	 **/
	private Vector specMethodDefs;

	/**
	 * The result of the translation
	 **/
	private Formula f;

	/*@
	  @ private invariant results != null;
	  @               &&  results.elemtype == \type(Formula);
	  @*/

	
	public FormulaWithSpecMethodDecl(Vector v, Formula f) {
		this.specMethodDefs = v;
		this.f = f;
	}
	
	/**
	 * Constructs a context form a formula, the context is empty.
	 * @param f formula resulting form the translation of an expression without 
	 * method call or from a expression that is a predicate.
	 **/
	public FormulaWithSpecMethodDecl(Formula f) {
		this(new Vector(), f);
	}

	/** Constructs a context from an existing context and a formula.
	 * @param c context that is taken into account, except its formula.
	 * @param f formula resulting form the translation of an expression without 
	 * method call or from a expression that is a predicate.
	 **/
	public FormulaWithSpecMethodDecl(FormulaWithSpecMethodDecl c, Formula f) {
		this(c, f, null);
	}

	public FormulaWithSpecMethodDecl(FormulaWithSpecMethodDecl c, Formula call, Formula decl) {
		this(c, null, call, decl);	
	}

	public FormulaWithSpecMethodDecl(FormulaWithSpecMethodDecl c1,
			FormulaWithSpecMethodDecl c2, Formula call, Formula decl) {
		this(c1, c2, null, call, decl);
		
	}
	
	public FormulaWithSpecMethodDecl(FormulaWithSpecMethodDecl c1,
			FormulaWithSpecMethodDecl c2, FormulaWithSpecMethodDecl c3, Formula call, Formula decl) {
		f = call;
		specMethodDefs = new Vector();
		if(c1 != null) {
			specMethodDefs.addAll(c1.specMethodDefs);
		}
		if(c2 != null) {
			specMethodDefs.addAll(c2.specMethodDefs);
		}
		if(c3 != null) {
			specMethodDefs.addAll(c3.specMethodDefs);
		}
		if(decl != null) {
			specMethodDefs.add(decl);
		}
		
		
	}


	/**
	 * Constructs a context from the translation of a binary operator.
	 * @param c1 context issued form the translation of one part.
	 * @param c2 context issued form the translation of the other part.
	 * @param f translation resulting formula
	 **/
	public FormulaWithSpecMethodDecl(
			FormulaWithSpecMethodDecl c1,
			FormulaWithSpecMethodDecl c2,
		Formula f) {
		this(c1, c2, f, null);
	}

	/**
	 * Constructs a context from the translation of a 3-ary operator.
	 * @param c1 context issued form the translation of a part.
	 * @param c2 context issued form the translation of another part.
	 * @param c3 context issued form the translation of another part.
	 * @param f translation resulting formula
	 **/
	public FormulaWithSpecMethodDecl(
			FormulaWithSpecMethodDecl c1,
			FormulaWithSpecMethodDecl c2,
			FormulaWithSpecMethodDecl c3,
		Formula f) {
		this(c1, c2, c3, f, null);
	}

	public Object clone() {
		Vector tmp = new Vector();
		Enumeration e = specMethodDefs.elements();
		while (e.hasMoreElements()) {
			Formula element = (Formula) e.nextElement();
			tmp.add(element.clone());
		}
		return new FormulaWithSpecMethodDecl(tmp, (Formula) getFormula().clone());
	}
	/**
	 * Returns the result of the translation.
	 * @return the formula quantified by the contextual part.
	 **/
	public Vector getPureMethodDef() {
		return specMethodDefs;
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
	specMethodDefs = res;
	}
	
	public void processIdent() {
		f.processIdent();
		Enumeration e = specMethodDefs.elements();
		while (e.hasMoreElements()) {
			Formula element = (Formula) e.nextElement();
			element.processIdent();
		}
	}
	
	public FormulaWithSpecMethodDecl sub(Formula a, Formula b, boolean subInCalledOld) {
		Formula tmpf, f  = getFormula().sub(a,b,subInCalledOld);
		boolean changed = f != getFormula();
		Vector tmp = new Vector();
		Enumeration e = specMethodDefs.elements();
		while (e.hasMoreElements()) {
			Formula element = (Formula) e.nextElement();
			tmpf = element.sub(a,b,subInCalledOld);
			changed = changed || tmpf != element;
			tmp.add(tmpf);
		}
		if (changed)
		return new FormulaWithSpecMethodDecl(tmp,f);
		else
			return this;
	}

	public FormulaWithSpecMethodDecl sub(Field a, Field b, boolean subInCalledOld) {
		Formula f1 = new TerminalForm(new Identifier(a));
		Formula f2 = new TerminalForm(new Identifier(b));
		return sub(f1, f2, subInCalledOld);

	}

	public FormulaWithSpecMethodDecl instancie(Formula  b) {
		f.instancie(b);
		Enumeration e = specMethodDefs.elements();
		while (e.hasMoreElements()) {
			Formula element = (Formula) e.nextElement();
			element.instancie(b);
		}
		return this;
	}

	private FormulaWithSpecMethodDecl renameParam(
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
				return (FormulaWithSpecMethodDecl) clone();
		}

	/**
	 * Instanciate the parameters
	 * @param signature
	 * @param newSignature
	 * @return the rightly instanciated formula with 
	 * 		parameters or this if newSignature is <code>null</code>
	 * @throws PogException
	 */
	//@ modifies \nothing;
	public FormulaWithSpecMethodDecl renameParam(IAParameters signature, Vector newSignature)
		throws PogException {
		if ((signature instanceof Parameters) && newSignature != null) {
			
			return renameParam(
					((Parameters) signature).signature.elements(),
					newSignature.elements());
		}
		else {
			return this;
		}
	}

}
