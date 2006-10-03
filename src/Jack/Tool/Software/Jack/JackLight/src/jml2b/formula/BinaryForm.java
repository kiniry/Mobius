//******************************************************************************
/* Copyright (c) 2002, 2003 GEMPLUS Software Research Labs. All Rights Reserved.
/* Copyright (c) 2003, 2004 INRIA. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: BinaryForm.java
/*
/*******************************************************************************
/* Warnings/Remarks:
/*  09/26/2003 : Simplify integration achieved
/******************************************************************************/
package jml2b.formula;

import java.util.Enumeration;
import java.util.Set;
import java.util.Vector;

import jml2b.exceptions.InternalError;
import jml2b.structure.java.Field;
import jml2b.structure.java.Identifier;
import jml2b.structure.java.Parameters;

/**
 * This class implements binary formula.
 * The token assoc	iated with those formulas can be
 * <UL>
 * <li> B_APPLICATION
 * <li> B_COUPLE
 * <li> B_FUNCTION_EQUALS
 * <li> B_IN
 * <li> B_INTERSECTION
 * <li> B_INTERVAL
 * <li> B_OVERRIDING
 * <li> B_SET_EQUALS
 * <li> B_SUBSTRACTIOn_DOM
 * <li> B_TOTALFUNCTION
 * <li> B_TOTALINJECTION
 * <li> B_UNION
 * <li> CONSTANT_FUNCTION
 * <li> EQUALS_ON_OLD_INSTANCES
 * <li> GUARDED_SET
 * <li> LOCAL_VAR_DECL
 * <li> Ja_COMMA
 * <li> Ja_ADD_OP
 * <li> Ja_MOD
 * <li> Ja_NEGATIVE_OP
 * <li> Ja_MUL_OP
 * <li> Ja_DIV_OP
 * <li> Ja_EQUAL_OP
 * <li> Ja_DIFFERENT_OP
 * <li> Ja_AND_OP
 * <li> Ja_OR_OP
 * <li> Ja_LE_OP
 * <li> Ja_LESS_OP
 * <li> Ja_GE_OP
 * <li> Ja_GREATER_OP
 * <li> Jm_IMPLICATION_OP
 * </UL>
 * @author L. Burdy
**/
public class BinaryForm extends Formula {

	/**
	 * Returns the default type declaration for a reference
	 * @return <code>REFENCES - (instances \/ {null})</code>
	 **/
	public static BinaryForm getDefaultRefDecl() {
		return new BinaryForm(
			Ja_NEGATIVE_OP,
			TerminalForm.REFERENCES,
			new BinaryForm(
				B_UNION,
				TerminalForm.instances,
				new UnaryForm(
					B_ACCOLADE,
					new TerminalForm(Ja_LITERAL_null, "null"))));
	}

	public static BinaryForm getDefaultRefDecl(Formula x) {
		return new BinaryForm(
			Ja_AND_OP,
			not(new BinaryForm(B_IN, x, TerminalForm.instances)),
			new BinaryForm(
				Ja_DIFFERENT_OP,
				x,
				new TerminalForm(Ja_LITERAL_null, "null")));
	}

	/**
	 * The left part of the binary formula.
	 **/
	protected Formula /*@ non_null @*/ left;

	/**
	 * The right part of the binary formula.
	 **/
	protected Formula /*@ non_null @*/ right;



	public BinaryForm(BinaryForm f) {
		super(f.getNodeType());
		this.left = f.left;
		this.right = f.right;
		if(left == null || right == null)
			throw new NullPointerException();
	}

	/**
	 * Constructs a binary formula from two formulas and a token.
	 * @param nodeType token of the new formula
	 * @param left left part of the new formula
	 * @param right right part of the new formula
	 **/
	/*@
	  @ requires left != null && right != null;
	  @*/
	public BinaryForm(byte nodeType, Formula left, Formula right) {
		super(nodeType);
		this.left = left;
		this.right = right;
		if(left == null || right == null)
			throw new NullPointerException();
	}

	/**
	 * Clones the formula
	 * @see Formula#clone()
	 **/
	public Object clone() {
		BinaryForm res =
			new BinaryForm(
				getNodeType(),
				(Formula) left.clone(),
				(Formula) right.clone());
		return res;
	}

	public void processIdent() {
		left.processIdent();
		right.processIdent();
	}

	public Formula instancie(Formula b) {
		left = left.instancie(b);
		right = right.instancie(b);
		if(left == null || right == null)
			throw new NullPointerException();
		return this;
	}

	public Formula sub(Formula a, Formula b, boolean subInCalledOld) {
		switch (getNodeType()) {
			case B_APPLICATION :
			case ARRAY_ACCESS :
				{
					if (a.getNodeType() == getNodeType()
						&& ((BinaryForm) a).left.equals(left)
						&& ((BinaryForm) a).right.equals(right))
						return b;
					Formula tmpleft = left.sub(a, b, subInCalledOld);
					Formula tmpright = right.sub(a, b, subInCalledOld);

					// Optimization : (a <+ { c |-> d })(c) is rewriting in d.
					if (tmpleft.getNodeType() == B_OVERRIDING) {
						Formula tmp = ((BinaryForm) tmpleft).right;
						if (tmp.getNodeType() == B_COUPLE) {
							if (((BinaryForm) tmp).left.equals(tmpright))
								return ((BinaryForm) tmp).right;
						}
					} else if (tmpleft == left && tmpright == right)
						return this;
					else
						return new BinaryForm(getNodeType(), tmpleft, tmpright);
				}
			default :
				Formula tmpleft = left.sub(a, b, subInCalledOld);
				Formula tmpright = right.sub(a, b, subInCalledOld);
				if (tmpleft == left && tmpright == right)
					return this;
				else
					return new BinaryForm(getNodeType(), tmpleft, tmpright);
		}
	}

	public Formula suppressSpecialOld(int token) {
		Formula tmpleft = left.suppressSpecialOld(token);
		Formula tmpright = right.suppressSpecialOld(token);
		if (tmpleft == left && tmpright == right)
			return this;
		else
			return new BinaryForm(getNodeType(), tmpleft, tmpright);
	}

	public Formula subIdent(String a, Formula b) {
		Formula tmpleft = left.subIdent(a, b);
		Formula tmpright = right.subIdent(a, b);
		switch (getNodeType()) {
			case Ja_ADD_OP :
				if (tmpright.getNodeType() == Ja_NUM_INT) {
					if (tmpleft.getNodeType() == Ja_ADD_OP
						&& ((BinaryForm) tmpleft).right.getNodeType()
							== Ja_NUM_INT)
						return new BinaryForm(
							Ja_ADD_OP,
							((BinaryForm) tmpleft).left,
							new TerminalForm(
								Ja_NUM_INT,
								(
									new Integer(
										((TerminalForm) ((BinaryForm) tmpleft)
									.right)
									.getNodeText())
									.intValue()
									+ new Integer(
										((TerminalForm) tmpright)
											.getNodeText())
										.intValue())
									+ ""));
					if (tmpleft.getNodeType() == Ja_NEGATIVE_OP
						&& ((BinaryForm) tmpleft).right.getNodeType()
							== Ja_NUM_INT)
						return new BinaryForm(
							Ja_ADD_OP,
							((BinaryForm) tmpleft).left,
							new TerminalForm(
								Ja_NUM_INT,
								(new Integer(((TerminalForm) tmpright)
									.getNodeText())
									.intValue()
									- new Integer(
										((TerminalForm) ((BinaryForm) tmpleft)
											.right)
											.getNodeText())
										.intValue())
									+ ""));
				}
			case Ja_NEGATIVE_OP :
				if (tmpright.getNodeType() == Ja_NUM_INT) {
					if (tmpleft.getNodeType() == Ja_ADD_OP
						&& ((BinaryForm) tmpleft).right.getNodeType()
							== Ja_NUM_INT)
						return new BinaryForm(
							Ja_NEGATIVE_OP,
							((BinaryForm) tmpleft).left,
							new TerminalForm(
								Ja_NUM_INT,
								(new Integer(((TerminalForm) tmpright)
									.getNodeText())
									.intValue()
									- new Integer(
										((TerminalForm) ((BinaryForm) tmpleft)
											.right)
											.getNodeText())
										.intValue())
									+ ""));
					if (tmpleft.getNodeType() == Ja_NEGATIVE_OP
						&& ((BinaryForm) tmpleft).right.getNodeType()
							== Ja_NUM_INT)
						return new BinaryForm(
							Ja_NEGATIVE_OP,
							((BinaryForm) tmpleft).left,
							new TerminalForm(
								Ja_NUM_INT,
								(
									new Integer(
										((TerminalForm) ((BinaryForm) tmpleft)
									.right)
									.getNodeText())
									.intValue()
									+ new Integer(
										((TerminalForm) tmpright)
											.getNodeText())
										.intValue())
									+ ""));
				}
			default :
				if ((getNodeType() == B_APPLICATION
					|| getNodeType() == ARRAY_ACCESS)
					&& tmpleft.getNodeType() == B_OVERRIDING) {
					Formula tmp = ((BinaryForm) tmpleft).right;
					if (tmp.getNodeType() == B_COUPLE) {
						if ((((BinaryForm) tmp).left).equals(tmpright)) {
							return ((BinaryForm) tmp).right;
						}
					}
				}
				if (tmpleft == left && tmpright == right)
					return this;
				else
					return new BinaryForm(getNodeType(), tmpleft, tmpright);
		}
	}

	public boolean equals(Object f) {
		return getNodeType() == ((Formula) f).getNodeType()
			&& left.equals(((BinaryForm) f).left)
			&& right.equals(((BinaryForm) f).right);
	}

		public int contains(Vector selectedFields) {
		return left.contains(selectedFields) + right.contains(selectedFields);
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
			Formula f1 = new TerminalForm(new Identifier(f));
			Object o = newSignature.nextElement();
			Formula f2;
			if (o instanceof String)
				f2 = new TerminalForm((String) o);
			else
				f2 = (Formula) o;
			//			f2.stateType = f.getType();
			return renameParam(signature, newSignature).sub(f1, f2, true);
		} else
			return (Formula) clone();
	}

	public Formula renameParam(Parameters signature, Vector newSignature) {
		return renameParam(
			signature.signature.elements(),
			newSignature.elements());
	}

	public boolean isObvious(boolean atTheEnd) {
		switch (getNodeType()) {
			case Ja_EQUALS_OP :
			case B_SET_EQUALS :
			case B_FUNCTION_EQUALS :
			case EQUALS_ON_OLD_INSTANCES :
			case EQUALS_ON_OLD_INSTANCES_ARRAY :
				return (
					left instanceof TerminalForm
						&& right instanceof TerminalForm
						&& ((TerminalForm) left).getNonAmbiguousName().equals(
							((TerminalForm) right).getNonAmbiguousName()))
					|| (atTheEnd
						&& left instanceof TerminalForm
						&& right instanceof UnaryForm
						&& right.getNodeType() == Jm_T_OLD
						&& ((UnaryForm) right).getExp() instanceof TerminalForm
						&& ((TerminalForm) left).getNonAmbiguousName().equals(
							((TerminalForm) ((UnaryForm) right).getExp())
								.getNonAmbiguousName()));
			case B_SUBSTRACTION_DOM :
				return right.isObvious(atTheEnd);
			case Jm_IMPLICATION_OP :
				return right.isObvious(atTheEnd) || left.isBFalse();
			case Ja_AND_OP :
			case Jm_AND_THEN :
				return left.isObvious(atTheEnd) && right.isObvious(atTheEnd);
			case Ja_OR_OP :
			case Jm_OR_ELSE :
				return left.isObvious(atTheEnd) || right.isObvious(atTheEnd);
			default :
				return false;
		}
	}

	public void garbageIdent() {
		if(left != null) {
			left.garbageIdent();
		}
		if(right != null) {
			right.garbageIdent();
		}
	}

	public Vector toVector() {
		Vector res = new Vector();
		if (getNodeType() == Ja_COMMA) {
			res = left.toVector();
			res.addAll(right.toVector());
		} else {
			res.add(this);
		}
		return res;
	}

	public void getFields(Set fields) {
		left.getFields(fields);
		right.getFields(fields);
	}

	/**
	 * Returns the left formula.
	 * @return <code>left</code>
	 */
	public Formula getLeft() {
		return left;
	}

	/**
	 * Returns the right formula.
	 * @return <code>right</code>
	 */
	public Formula getRight() {
		return right;
	}

	static final long serialVersionUID = 6458770229124292163L;

	public BasicType getBasicType() {
		switch (getNodeType()) {
			case B_APPLICATION :
			case ARRAY_ACCESS :
				return left.getBasicType().getRtype();
			case LOCAL_VAR_DECL :
			case LOCAL_ELEMENTS_DECL :
			case Ja_OR_OP :
			case Jm_OR_ELSE :
			case Ja_DIFFERENT_OP :
			case Ja_AND_OP :
			case Jm_AND_THEN :
			case Jm_IMPLICATION_OP :
			case Ja_EQUALS_OP :
			case Ja_LE_OP :
			case Ja_LESS_OP :
			case Ja_GE_OP :
			case Ja_GREATER_OP :
			case B_IN :
			case Jm_IS_SUBTYPE :
			case B_SET_EQUALS :
			case EQUALS_ON_OLD_INSTANCES :
			case EQUALS_ON_OLD_INSTANCES_ARRAY :
			case B_SUBSTRACTION_DOM :
			case B_FUNCTION_EQUALS :
			case INTERSECTION_IS_NOT_EMPTY :
				return BasicType.PropType;
			case Ja_ADD_OP :
			case Ja_NEGATIVE_OP :
			case Ja_MUL_OP :
			case Ja_DIV_OP :
			case Ja_MOD :
				return BasicType.ZType;
			case B_UNION :
				return left.getBasicType();
			case B_COUPLE :
				return new BasicType(left.getBasicType(), right.getBasicType());
				case ALL_ARRAY_ELEMS :
					return new BasicType(left.getBasicType().getRtype().getRtype(), BasicType.PropType);
			case Ja_COMMA :
				return null;
			case B_INTERVAL :
				return new BasicType(BasicType.ZType, BasicType.PropType);
			case B_OVERRIDING :
				return left.getBasicType();
			case GUARDED_SET :
				return left.getBasicType();
			default :
				throw new InternalError(
					"BinaryForm.getBasicType(): unhandled case: "
						+ toString[getNodeType()]);
		}
	}

}