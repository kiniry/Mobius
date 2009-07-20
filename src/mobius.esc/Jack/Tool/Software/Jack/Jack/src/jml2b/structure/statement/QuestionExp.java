//******************************************************************************
/* Copyright (c) 2002, 2003 GEMPLUS Software Research Labs. All Rights Reserved.
/* Copyright (c) 2003, 2004 INRIA. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: QuestionExp.java
/*
/*******************************************************************************
/* Warnings/Remarks:
/*  09/26/2003 : Simplify integration achieved
/******************************************************************************/

package jml2b.structure.statement;

import java.util.Set;
import java.util.Vector;

import jml2b.IJml2bConfiguration;
import jml2b.exceptions.Jml2bException;
import jml2b.exceptions.LinkException;
import jml2b.exceptions.PogException;
import jml2b.exceptions.TypeCheckException;
import jml2b.formula.BinaryForm;
import jml2b.formula.Formula;
import jml2b.formula.TerminalForm;
import jml2b.formula.TriaryForm;
import jml2b.link.LinkContext;
import jml2b.link.LinkInfo;
import jml2b.pog.lemma.ExceptionalBehaviourStack;
import jml2b.pog.lemma.FormulaWithSpecMethodDecl;
import jml2b.pog.lemma.Proofs;
import jml2b.pog.lemma.VirtualFormula;
import jml2b.pog.util.ColoredInfo;
import jml2b.structure.java.Field;
import jml2b.structure.java.JmlFile;
import jml2b.structure.java.Modifiers;
import jml2b.structure.java.ParsedItem;
import jml2b.structure.java.Type;
import jml2b.structure.jml.JmlExpression;
import jml2b.util.ModifiableSet;
import antlr.collections.AST;

/**
 * This class implements a question expression, that is <code>a ? b :c </code>
 * @author L. Burdy
 **/
public class QuestionExp extends Expression {

	/**
	 * The condition
	 **/
	private Expression cond;

	/**
	 * The value of the expression when the condition is true
	 **/
	private Expression left;

	/**
	 * The value of the expression when the condition is false
	 **/
	private Expression right;

	/*@
	  @ invariant parsed ==> cond != null
	  @        && parsed ==> left != null
	  @        && parsed ==> right != null;
	  @*/

	/**
	 * Constructs an expression as a <i>parsed item</i>.
	 * @param jf The file where the statement is located
	 * @param tree The <code>AST</code> node corresponding to the statement
	 * @see jml2b.structure.java.ParsedItem#ParsedItem(JmlFile, AST)
	 **/
	protected QuestionExp(JmlFile jf, AST tree) {
		super(jf, tree);
	}

	/**
	 * Constructs a question expression form another one
	 * @param nodeType The node type
	 * @param nodeText The node text
	 * @param cond The condition
	 * @param left The first expression
	 * @param right The second expression
	 **/
	/*@
	  @ requires cond != null && left != null && right != null;
	  @ ensures parsed;
	  @*/
	private QuestionExp(
		int nodeType,
		String nodeText,
		Expression cond,
		Expression left,
		Expression right) {
		super(nodeType, nodeText);
		this.cond = cond;
		this.left = left;
		this.right = right;
		//@ set parsed = true;
	}

	public boolean equals(Expression e) {
		return getNodeType() == e.getNodeType()
			&& cond.equals(((QuestionExp) e).cond)
			&& left.equals(((QuestionExp) e).left)
			&& right.equals(((QuestionExp) e).right);
	}

	public Object clone() {
		QuestionExp res =
			new QuestionExp(
				getNodeType(),
				getNodeText(),
				(Expression) cond.clone(),
				(Expression) left.clone(),
				(Expression) right.clone());
		res.setBox(this);
		res.setStateType(getStateType());
		return res;
	}

	FormulaWithSpecMethodDecl exprToContextForm(
		IJml2bConfiguration config,
		Vector methods,
		boolean pred)
		throws Jml2bException, PogException {
		FormulaWithSpecMethodDecl l = left.exprToContextForm(config, methods, pred);
		FormulaWithSpecMethodDecl r = right.exprToContextForm(config, methods, pred);
		FormulaWithSpecMethodDecl c = cond.exprToContextForm(config, methods, true);
		TriaryForm res =
			new TriaryForm(
				Ja_QUESTION,
				c.getFormula(),
				l.getFormula(),
				r.getFormula());
		return new FormulaWithSpecMethodDecl(c, l, r, res);

	}

	public String toJava(int indent) {
		return cond.toJava(indent)
			+ " ? "
			+ left.toJava(indent)
			+ " : "
			+ right.toJava(indent);
	}

	/*@
	  @ modifies cond, left, right;
	  @ ensures cond != null && left != null && right != null;
	  @*/
	public AST parse(AST tree) throws Jml2bException {
		cond = Expression.createE(getJmlFile(), tree.getFirstChild());
		cond.parse(tree.getFirstChild());
		left =
			Expression.createE(
				getJmlFile(),
				tree.getFirstChild().getNextSibling());
		AST subtree = left.parse(tree.getFirstChild().getNextSibling());
		right = Expression.createE(getJmlFile(), subtree);
		right.parse(subtree);
		//@ set parsed = true;
		return tree.getNextSibling();
	}

	public LinkInfo linkStatement(IJml2bConfiguration config, LinkContext f)
		throws Jml2bException {
		LinkInfo l_id, r_id;

		cond.linkStatement(config, f);

		l_id = left.linkStatement(config, f);
		r_id = right.linkStatement(config, f);

		if (l_id == null) {
			// assumes that we have both null
			// should not happen
			return null;
		}

		if (l_id.tag == LinkInfo.TYPE) {

			LinkInfo max;

			// renvoie l'un des deux (le plus grand)
			if (l_id.type.isSubtypeOf(config, r_id.type)) {
				max = r_id;
			} else {
				max = l_id;
			}
			setStateType(max.getType());
			return max;
		}

		return null;
	}

	public Type typeCheck(IJml2bConfiguration config, LinkContext f)
		throws Jml2bException {
		Type t1 = cond.typeCheck(config, f);
		Type t2 = left.typeCheck(config, f);
		Type t3 = right.typeCheck(config, f);
		if (!t1.isBoolean())
			throw new TypeCheckException(
				"Type mismatch: cannot convert from "
					+ t1.toJava()
					+ " to boolean",
				cond);
		if (t2.isBoolean() && t3.isBoolean())
			return t2;
		if (t2.isNumeric() && t3.isNumeric()) {
			if (t1.getTag() == Type.T_BYTE && t2.getTag() == Type.T_SHORT)
				return t2;
			if (t2.getTag() == Type.T_BYTE && t1.getTag() == Type.T_SHORT)
				return t1;
			if ((t1.getTag() == Type.T_BYTE
				|| t1.getTag() == Type.T_SHORT
				|| t1.getTag() == Type.T_CHAR)
				&& t2.getTag() == Type.T_INT)
				return t1;
			if ((t2.getTag() == Type.T_BYTE
				|| t2.getTag() == Type.T_SHORT
				|| t2.getTag() == Type.T_CHAR)
				&& t1.getTag() == Type.T_INT)
				return t2;
			return Type.binaryNumericPromotion(t1, t2);
		}
		if (t2.isRef() && t3.isRef()) {
			if (t2.getTag() == Type.T_NULL)
				return t3;
			if (t3.getTag() == Type.T_NULL)
				return t2;
			if (t2.isSubtypeOf(config, t3))
				return t3;
			if (t3.isSubtypeOf(config, t2))
				return t2;
			throw new TypeCheckException(
				"Incompatible conditionnal operand types "
					+ t2.toJava()
					+ " and "
					+ t3.toJava(),
				this);
		}
		if (t2.getTag() == Type.T_TYPE && t3.getTag() == Type.T_TYPE)
			return t2;
		throw new TypeCheckException(
			"Incompatible conditionnal operand types "
				+ t2.toJava()
				+ " and "
				+ t3.toJava(),
			this);
	}

	public void processIdent() {
		cond.processIdent();
		left.processIdent();
		right.processIdent();
	}

	public void isModifiersCompatible(IJml2bConfiguration config, Modifiers modifiers)
		throws LinkException {
		cond.isModifiersCompatible(config, modifiers);
		left.isModifiersCompatible(config, modifiers);
		right.isModifiersCompatible(config, modifiers);
	}

	public JmlExpression instancie() {
		cond = (Expression) cond.instancie();
		left = (Expression) left.instancie();
		right = (Expression) right.instancie();
		return this;
	}

	public Expression subField(Field f, Field newF) {
		cond = cond.subField(f, newF);
		left = left.subField(f, newF);
		right = right.subField(f, newF);
		return this;
	}

	public Expression subResult(String ww) {
		cond = cond.subResult(ww);
		left = left.subResult(ww);
		right = right.subResult(ww);
		return this;
	}

	public JmlExpression instancie(Expression b) {
		cond = (Expression) cond.instancie(b);
		left = (Expression) left.instancie(b);
		right = (Expression) right.instancie(b);
		return this;
	}

	public Vector getParsedItems() {
		Vector res = cond.getParsedItems();
		res.addAll(left.getParsedItems());
		res.addAll(right.getParsedItems());
		res.add((ParsedItem) this);
		return res;
	}

	public void setParsedItem(ParsedItem pi) {
		cond.setParsedItem(pi);
		left.setParsedItem(pi);
		right.setParsedItem(pi);
		change(pi);
	}

	public boolean isConstant() {
		return cond.isConstant() && left.isConstant() && right.isConstant();
	}

	//@ requires hasValue();
	public int getValue() {
		return (cond.getValue() != 0) ? left.getValue() : right.getValue();
	}

	//	Vector getFreshVars() {
	//		return new Vector();
	//	}

	public void old() {
		cond.old();
		left.old();
		right.old();
	}

	public Proofs wp(
		IJml2bConfiguration config,
		String result,
		Proofs normalBehaviour,
		ExceptionalBehaviourStack exceptionalBehaviour)
		throws Jml2bException, PogException {
		Proofs lThen =
			left.wp(config, result, normalBehaviour, exceptionalBehaviour);
		Proofs lElse =
			right.wp(config, result, normalBehaviour, exceptionalBehaviour);

		// vv is a temporary variable that stores the condition evaluation
		String vv = fresh();

		// s1 = vv == true
		Formula s1 =
			new BinaryForm(
				Ja_EQUALS_OP,
				new TerminalForm(vv),
				new TerminalForm(Ja_LITERAL_true));

		// s2 = vv = false
		Formula s2 =
			new BinaryForm(
				Ja_EQUALS_OP,
				new TerminalForm(vv),
				new TerminalForm(Ja_LITERAL_false));

		lThen.addHyp(
			s1,
			new ColoredInfo(cond, ColoredInfo.IS_TRUE),
			VirtualFormula.LOCALES);
		lElse.addHyp(
			s2,
			new ColoredInfo(cond, ColoredInfo.IS_FALSE),
			VirtualFormula.LOCALES);
		lThen.addAll(lElse);
		return cond.wp(config, vv, lThen, exceptionalBehaviour);
	}

	public void getPrecondition(
		IJml2bConfiguration config,
		ModifiableSet modifies,
		Vector req,
		Vector ens)
		throws Jml2bException, PogException {
		cond.getPrecondition(config, modifies, req, ens);
		left.getPrecondition(config, modifies, req, ens);
		right.getPrecondition(config, modifies, req, ens);
	}

	public void collectCalledMethod(Vector calledMethod) {
		cond.collectCalledMethod(calledMethod);
		left.collectCalledMethod(calledMethod);
		right.collectCalledMethod(calledMethod);
	}
	
	static final long serialVersionUID = -5341421445214593422L;

	void getFreeVariable(Set s) {
		cond.getFreeVariable(s);
		left.getFreeVariable(s);
		right.getFreeVariable(s);

	}

	/**
	 * @return
	 */
	public Expression getCond() {
		return cond;
	}

	/**
	 * @return
	 */
	public Expression getLeft() {
		return left;
	}

	/**
	 * @return
	 */
	public Expression getRight() {
		return right;
	}

}
