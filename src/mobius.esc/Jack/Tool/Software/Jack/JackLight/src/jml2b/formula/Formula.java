//******************************************************************************
/* Copyright (c) 2002, 2003 GEMPLUS Software Research Labs. All Rights Reserved.
/* Copyright (c) 2003, 2004 INRIA. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: Formula.java
/*
/*******************************************************************************
/* Warnings/Remarks:
/*  09/26/2003 : Simplify integration achieved
/******************************************************************************/
package jml2b.formula;

import java.io.Serializable;
import java.util.Enumeration;
import java.util.Set;
import java.util.Vector;

import jml2b.exceptions.PogException;
import jml2b.pog.lemma.FormulaWithPureMethodDecl;
import jml2b.structure.IAParameters;
import jml2b.structure.java.Field;
import jml2b.structure.java.Identifier;
import jml2b.structure.java.Parameters;
import jml2b.util.Profiler;

/**
 * This class describes a formula.
 * A formula is the content of a lemma : an hypothesis or a goal.
 * @author L. Burdy
 */
abstract public class Formula
	extends Profiler
	implements IFormToken, Serializable {

	/**
	 * Returns the formula <code>null</code>.
	 * @return the formula <code>null</code>
	 **/
	public static Formula getNull() {
		return new TerminalForm(Ja_LITERAL_null, "null");
	}

	/**
	 * Returns the formula <code>false</code>.
	 * @return the formula <code>false</code>
	 **/
	public static Formula getFalse() {
		return new TerminalForm(Ja_LITERAL_false);
	}

	/**
	 * Returns the disjunctive formula between the two parameters.
	 * @param s1 left disjonctive formula
	 * @param s2 right disjonctive formula
	 * @return the formula <code>s1 || s2</code>
	 **/
	public static BinaryForm or(Formula s1, Formula s2) {
		return new BinaryForm(Ja_OR_OP, s1, s2);
	}

	/**
	 * Returns the formula corresponding to a field declaration.
	 * @param f Field to declare.
	 * @return
	 */
	public static Formula declarField(Field f) {
		if (f.getType().isBuiltin())
			return new BinaryForm(
				LOCAL_VAR_DECL,
				new TerminalForm(new Identifier(f)),
				new TTypeForm(IFormToken.T_TYPE, f.getType()));
		else
			return new BinaryForm(
				Ja_AND_OP,
				new BinaryForm(
					LOCAL_VAR_DECL,
					new TerminalForm(new Identifier(f)),
					TerminalForm.REFERENCES),
				new BinaryForm(
					Ja_AND_OP,
					new BinaryForm(
						B_IN,
						new TerminalForm(new Identifier(f)),
						new BinaryForm(
							B_UNION,
							TerminalForm.instances,
							new UnaryForm(
								B_ACCOLADE,
								new TerminalForm(Ja_LITERAL_null, "null")))),
					new BinaryForm(
						Jm_IMPLICATION_OP,
						new BinaryForm(
							Ja_DIFFERENT_OP,
							new TerminalForm(new Identifier(f)),
							new TerminalForm(Ja_LITERAL_null, "null")),
						new BinaryForm(
							Jm_IS_SUBTYPE,
							new BinaryForm(
								B_APPLICATION,
								TerminalForm.typeof,
								new TerminalForm(new Identifier(f))),
							new TTypeForm(
								IFormToken.Jm_T_TYPE,
								f.getType())))));

	}

	/**
	 * Returns the conjunctive formula between the two parameters.
	 * @param s1 left conjonctive formula
	 * @param s2 right conjonctive formula
	 * @return the formula <code>s1 && s2</code>
	 **/
	public static BinaryForm and(Formula s1, Formula s2) {
		return new BinaryForm(Ja_AND_OP, s1, s2);
	}

	/**
	 * Returns the negation of the parameter.
	 * @param s1 negated formula
	 * @return the formula <code>! s1</code>
	 **/
	public static UnaryForm not(Formula s1) {
		return new UnaryForm(Ja_LNOT, s1);
	}

	/**
	 * Returns the implicative formula between the two parameters.
	 * @param s1 left implicative formula
	 * @param s2 right implicative formula
	 * @return the formula <code>s1 ==> s2</code>
	 **/
	public static BinaryForm implies(Formula s1, Formula s2) {
		return new BinaryForm(Jm_IMPLICATION_OP, s1, s2);
	}

	/**
	 * Returns the string containing white spaces corresponding to an 
	 * indentation
	 * @param i The indentation number
	 * @return a string with a carriage return and <code>i</code> white spaces.
	 **/
	public static String indent(int i) {
		String res = "\n";
		for (int j = 0; j < i; j++)
			res += " ";
		return res;
	}

	/**
	 * token describing this formula.
	 **/
	private byte nodeType;

	/*@
	  @ protected invariant nodeType != null;
	  @ protected invariant nodeType == Ja_EQUAL_OP 
	  @                     ==> \typeof(this) <: \type(BinaryForm);
	  @ protected invariant nodeType == Jm_T_TYPE 
	  @                     ==> \typeof(this) <: \type(TTypeForm);
	  @ protected invariant nodeType == T_CALLED_OLD 
	  @                     ==> \typeof(this) <: \type(UnaryForm);
	  @ protected invariant (\forall Formula f; nodeType == f.nodeType 
	  @                                        ==> \typeof(this) == \typeof(f));
	  @*/

	/**
	 * Creates a formula with a given node type.
	 * @param nodeType the node type
	 **/
	Formula(byte nodeType) {
		this.nodeType = nodeType;
	}

	/**
	 * Returns the type of a formula
	 * @return The basic type of ta formula.
	 */
	public abstract BasicType getBasicType();

	/**
	 * Clones the formula.
	 * @return the cloned formula
	 **/
	public abstract Object clone();

	/**
	 * Collects all the indentifier of a formula to give them an index in the 
	 * identifer array. This array is then analyzed to give short name when it
	 * is possible to identifiers.
	 * @see jml2b.pog.IdentifierResolver#bIdents
	 **/
	public abstract void processIdent();

	/** 
	 * Replaces <code>this</code> with the parameter in the expression.
	 * @param b expression on which the method where the expression occurs is 
	 * called.
	 * @return the modified expression
	 **/
	public abstract Formula instancie(Formula b);

	/**
	 * Collects the fields that occur in the formula.
	 * @param fields The set a collected fields.
	 **/
	public abstract void getFields(Set fields);

	/**
	 * Applies a substitution on a formula.
	 * @param a the substituted formula
	 * @param b the new formula
	 * @param subInCalledOld specify whether the substitution should also be 
	 * applied in the <i>called old</i> construction
	 * @return the formula when the substitution has been applied.
	 **/
	/*@
	  @ requires a != null;
	  @ ensures \result != null;
	  @*/
	public abstract Formula sub(Formula a, Formula b, boolean subInCalledOld);

	/**
	 * Suppress the <i>called old</i> pragmas.
	 * <i>old</i> pragma are substitued with <i>called old</i> into the
	 * specification of a called method in manner to be differentiated from
	 * the <i>old</i> pragma of the current method.
	 * After the treatment, the <i>called old</i> pragmas are suppressed.
	 * @return the formula with suppressed <i>called old</i> pragmas
	 **/
	public abstract Formula suppressSpecialOld(int token);

	/**
	 * Applies a substitution on a formula.
	 * @param a the substituted string correspondingto an identifier
	 * @param b the new formula
	 * @return the formula when the substitution has been applied.
	 **/
	//@ ensures \result != null;
	public abstract Formula subIdent(String a, Formula b);

	/**
	 * Returns whether the formula equals the parameter.
	 * @param f the checked parameter
	 * @return <code>true</code> if the formula syntaxically equals the 
	 * parameter, <code>false</code> otherwise
	 **/
	public abstract boolean equals(Object f);

	/**
	 * Returns whether a formula is obvious.
	 * @return <code>true</code> if the formula is considered as obvious,
	 * <code>false</code> otherwise
	 **/
	public abstract boolean isObvious(boolean atTheEnd);

	/**
	 * Annotates all the fields that appear in the formula to declare them in 
	 * the Atelier B files.
	 **/
	public abstract void garbageIdent();

	public abstract int contains(Vector selectedFields);

	/**
	 * Encapsulates given parameters into an <code>old</code> pragma.
	 * @param signature the signature of a called method
	 * @return the formula when the parameters have been encapsulated
	 **/
	//@ ensures \result != null;
	public Formula oldParam(Vector signature) {
		Formula res = (Formula) clone();
		Enumeration e = signature.elements();
		while (e.hasMoreElements()) {
			Field f = (Field) e.nextElement();
			Formula s = new UnaryForm(Jm_T_OLD, new TerminalForm(new Identifier(f)));
			res = res.subIdent(f.getBName(), s);
		}
		return res;
	}

	/**
	 * Applies a substitution on a formula.
	 * @param a the substituted field
	 * @param b the new field
	 * @param subInCalledOld specify whether the substitution should also be 
	 * applied in the <i>called old</i> construction
	 * @return the formula when the substitution has been applied.
	 **/
	public Formula sub(Field a, Field b, boolean subInCalledOld) {
		Formula f1 = new TerminalForm(new Identifier(a));
		Formula f2 = new TerminalForm(new Identifier(b));
		return sub(f1, f2, subInCalledOld);

	}

	/**
	 * Renames the fields belonging to the parameter list with new names.
	 * @param signature the signature of the called method
	 * @param newSignature the list of new names
	 * @return the current formula renamed
	 * @see jml2b.pog.Proofs#renameParam(Parameters, Vector)
	 **/
	private Formula renameParam(
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
			return (Formula) clone();
	}

	/**
	 * Renames the fields belonging to the parameter list with new names.
	 * @param signature the signature of the called method
	 * @param newSignature the list of new names
	 * @return the current formula renamed
	 * @see jml2b.pog.Proofs#renameParam(Parameters, Vector)
	 **/
	public Formula renameParam(IAParameters signature, Vector newSignature)
		throws PogException {
		if (signature instanceof Parameters)
		return renameParam(
			((Parameters) signature).signature.elements(),
			newSignature.elements());
		else
			return this;
//		else
//			throw new jml2b.exceptions.InternalError("Formula.renameParam");
	}

	/**
	 * Returns whether a formula corresponds to <i>bfalse</i>
	 * @return <code>true</code> when the formula is <code>false == true</code>
	 * or <code>true == false</code>, <code>false</code> otherwise.
	 **/
	public boolean isBFalse() {
		return nodeType == Ja_EQUALS_OP
			&& ((((BinaryForm) this).getLeft().nodeType == Ja_LITERAL_false
				&& ((BinaryForm) this).getRight().nodeType == Ja_LITERAL_true)
				|| (((BinaryForm) this).getLeft().nodeType == Ja_LITERAL_true
					&& ((BinaryForm) this).getRight().nodeType
						== Ja_LITERAL_false));
	}

	/** 
	 * Returns whether a formula matches with an equality with 
	 * <code>null</code>
	 * @return <code>true</code> if the formula matches with 
	 * <code>a == null</code>, <code>false</code> otherwise.
	 **/
	public boolean matchAEqualsNull() {
		return nodeType == Ja_EQUALS_OP
			&& ((BinaryForm) this).getRight().nodeType == Ja_LITERAL_null;
	}

	/** 
	 * Converts comma separated formulas into a set of formulas.
	 * @return the vector containing comme separated formulas
	 * @see BinaryForm#toVector()
	 **/
	public Vector toVector() {
		Vector res = new Vector();
		res.add(this);
		return res;
	}

	/**
	 * Applies successive domain restriction to the formula
	 * @param df set of formula from which the formula should be restricted.
	 * @return the formula with domain restricted with the set of given 
	 * formulas
	 **/
	public FormulaWithPureMethodDecl domainRestrict(Vector df) {
		FormulaWithPureMethodDecl res = new FormulaWithPureMethodDecl(this);
		Enumeration e = df.elements();
		while (e.hasMoreElements()) {
			FormulaWithPureMethodDecl f = (FormulaWithPureMethodDecl) e.nextElement();
			res = new FormulaWithPureMethodDecl(f, res, new BinaryForm(B_SUBSTRACTION_DOM, f.getFormula(), res.getFormula()));
		}
		return res;
	}

	/**
	 * Returns the nodeType.
	 * @return byte
	 */
	public byte getNodeType() {
		return nodeType;
	}

	static final long serialVersionUID = 2912250853358401101L;

}