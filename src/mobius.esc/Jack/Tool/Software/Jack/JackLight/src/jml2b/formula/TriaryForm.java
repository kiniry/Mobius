//******************************************************************************
/* Copyright (c) 2002, 2003 GEMPLUS Software Research Labs. All Rights Reserved.
/* Copyright (c) 2003, 2004 INRIA. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: QuestionForm.java
/*
/*******************************************************************************
/* Warnings/Remarks:
/*  09/26/2003 : Simplify integration achieved
/******************************************************************************/
package jml2b.formula;

import java.util.Set;
import java.util.Vector;

/**
 * This class implements tri-ary formula, that is conditional formula coming 
 * from the Java structure <code>a ? b : c</code> or equals with restricted
 * domains formulas.
 * The token associated with those formulas can be
 * <UL>
 * <li> <code>Ja_QUESTION</code>
 * <li> <code>EQUALS_RESTRICT_DOM</code>
 * <li> <code>EQUAL_SUBSTRACTION_DOM</code>
 * </UL>
 * @author L. Burdy
 **/
public class TriaryForm extends Formula {

	/**
	 * 
	 */
	private static final long serialVersionUID = 1L;

	/**
	 * The condition or the restriction formula
	 **/
	protected Formula f1;

	/**
	 * The formula corresponding to a valid condition or the left restricted
	 * formula
	 **/
	protected Formula left;

	/**
	 * The formula corresponding to a unvalid condition or the right restricted
	 * formula
	 **/
	protected Formula right;

	/*@
	  @ private invariant f1 != null;
	  @                && left != null;
	  @                && right != null;
	  @*/

		public TriaryForm(TriaryForm f) {
		super(f.getNodeType());
		f1 = f.f1;
		this.left = f.left;
		this.right = f.right;
	}

	/**
	 * Constructs a question formula from three formulas.
	 * @param cond The condition formula
	 * @param left The formula corresponding to a valid condition
	 * @param right The formula corresponding to a unvalid condition
	 **/
	/*@
	  @ requires cond != null && left != null && right != null
	  @*/
	public TriaryForm(
		byte nodeType,
		Formula cond,
		Formula left,
		Formula right) {
		super(nodeType);
		f1 = cond;
		this.left = left;
		this.right = right;
	}

	public Object clone() {
		return new TriaryForm(
			getNodeType(),
			(Formula) f1.clone(),
			(Formula) left.clone(),
			(Formula) right.clone());
	}

	public void processIdent() {
		f1.processIdent();
		left.processIdent();
		right.processIdent();
	}

	public Formula instancie(Formula b) {
		f1 = f1.instancie(b);
		left = left.instancie(b);
		right = right.instancie(b);
		return this;
	}

	public Formula sub(Formula a, Formula b, boolean subInCalledOld) {
		Formula tmpcond = f1.sub(a, b, subInCalledOld);
		Formula tmpleft = left.sub(a, b, subInCalledOld);
		Formula tmpright = right.sub(a, b, subInCalledOld);
		if (tmpcond == f1 && tmpleft == left && tmpright == right)
			return this;
		else
			return new TriaryForm(getNodeType(), tmpcond, tmpleft, tmpright);
	}

	public Formula suppressSpecialOld(int token) {
		Formula tmpcond = f1.suppressSpecialOld(token);
		Formula tmpleft = left.suppressSpecialOld(token);
		Formula tmpright = right.suppressSpecialOld(token);
		if (tmpcond == f1 && tmpleft == left && tmpright == right)
			return this;
		else
			return new TriaryForm(getNodeType(), tmpcond, tmpleft, tmpright);
	}

	public Formula subIdent(String a, Formula b) {
		Formula tmpcond = f1.subIdent(a, b);
		Formula tmpleft = left.subIdent(a, b);
		Formula tmpright = right.subIdent(a, b);
		if (tmpcond == f1 && tmpleft == left && tmpright == right)
			return this;
		else
			return new TriaryForm(getNodeType(), tmpcond, tmpleft, tmpright);
	}

	public boolean equals(Object f) {
		return f instanceof TriaryForm
			&& getNodeType() == ((TriaryForm) f).getNodeType()
			&& f1.equals(((TriaryForm) f).f1)
			&& left.equals(((TriaryForm) f).left)
			&& right.equals(((TriaryForm) f).right);
	}

	public int contains(Vector selectedFields) {
		return f1.contains(selectedFields)
			+ left.contains(selectedFields)
			+ right.contains(selectedFields);
	}

	public boolean isObvious(boolean atTheEnd) {
		switch (getNodeType()) {
			case B_ARRAY_EQUALS :
			case Ja_QUESTION :
			case NEW_OBJECT :
				return false;
			default :
				throw new InternalError(
					"TriaryForm.isObvious() bad node type:" + getNodeType());
		}
	}


	public void garbageIdent() {
		f1.garbageIdent();
		left.garbageIdent();
		right.garbageIdent();
	}

	public void getFields(Set fields) {
		f1.getFields(fields);
		left.getFields(fields);
		right.getFields(fields);
	}

	/**
	 * Returns the f1.
	 * @return Formula
	 */
	public Formula getF1() {
		return f1;
	}

	/**
	 * Returns the left.
	 * @return Formula
	 */
	public Formula getLeft() {
		return left;
	}

	/**
	 * Returns the right.
	 * @return Formula
	 */
	public Formula getRight() {
		return right;
	}

	/* (non-Javadoc)
	 * @see jml2b.formula.Formula#getBasicType()
	 */
	public BasicType getBasicType() {
		switch (getNodeType()) {
			case B_ARRAY_EQUALS :
			case NEW_OBJECT :
				return BasicType.PropType;

			case ARRAY_RANGE :
				return new BasicType(
					f1.getBasicType().getRtype().getRtype(),
					BasicType.PropType);

			case Ja_QUESTION :
				return left.getBasicType();

			default :
				throw new InternalError(
					"TriaryForm.getBasicType: case not implemented: "
						+ toString[getNodeType()]);

		}

	}

}
