//******************************************************************************
/* Copyright (c) 2002, 2003 GEMPLUS Software Research Labs. All Rights Reserved.
/* Copyright (c) 2003, 2004 INRIA. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: 
/*
/*******************************************************************************
/* Warnings/Remarks:
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
import jml2b.link.LinkContext;
import jml2b.link.LinkInfo;
import jml2b.pog.lemma.FormulaWithPureMethodDecl;
import jml2b.structure.java.Field;
import jml2b.structure.java.JmlFile;
import jml2b.structure.java.Modifiers;
import jml2b.structure.java.ParsedItem;
import jml2b.structure.java.Type;
import jml2b.structure.jml.JmlExpression;
import jml2b.util.ModifiableSet;
import antlr.collections.AST;

/**
 * This class implements subtype JML expression, it corresponds to code like
 * <code>a <: b</code>
 * @author L. Burdy, A. Requet
 **/
public class IsSubtypeOfExp extends Expression {

	/**
	 * The tested subtype.
	 **/
	private Expression subType;

	/**
	 * The tested super type.
	 **/
	private Expression type;

	/*@
	  @ invariant parsed ==> subType != null
	  @        && parsed ==> type != null;
	  @*/

	/**
	 * Constructs an expression as a <i>parsed item</i>.
	 * @param jf The file where the statement is located
	 * @param tree The <code>AST</code> node corresponding to the statement
	 * @see jml2b.structure.java.ParsedItem#ParsedItem(JmlFile, AST)
	 **/
	IsSubtypeOfExp(JmlFile jf, AST tree) {
		super(jf, tree);
	}

	/**
	 * Constructs a subtype expression form another one
	 * @param nodeType The node type
	 * @param nodeText The node text
	 * @param type The super type
	 * @param subtype The subtype
	 **/
	/*@
	  @ requires type != null && subtype != null;
	  @*/
	IsSubtypeOfExp(
		int nodeType,
		String nodeText,
		Expression type,
		Expression subType) {
		super(nodeType, nodeText);
		this.type = type;
		this.subType = subType;
		//@ set parsed = true;
	}

	public Object clone() {
		IsSubtypeOfExp res =
			new IsSubtypeOfExp(getNodeType(), getNodeText(), type, subType);
		res.setBox(this);
		res.setStateType(getStateType());
		return res;
	}

	public boolean equals(Expression e) {
		return getNodeType() == e.getNodeType()
			&& type.equals(((IsSubtypeOfExp) e).type)
			&& subType.equals(((IsSubtypeOfExp) e).subType);
	}

	FormulaWithPureMethodDecl exprToContextForm(
		IJml2bConfiguration config,
		Vector methods,
		boolean pred)
		throws Jml2bException, PogException {
		FormulaWithPureMethodDecl s =
			subType.exprToContextForm(config, methods, false);
		FormulaWithPureMethodDecl t =
			type.exprToContextForm(config, methods, false);
		BinaryForm res =
			new BinaryForm(Jm_IS_SUBTYPE, s.getFormula(), t.getFormula());
		// res.box = (ParsedItem) this;
		return new FormulaWithPureMethodDecl(s, t, res);

	}

	public String toJava(int indent) {
		String r = subType.toJava(indent);
		return r + "<:" + type.toJava(indent + r.length() + 2);
	}

	/*@
	  @ modifies subType, type;
	  @ ensures subType != null && type != null;
	  @*/
	public AST parse(AST tree) throws Jml2bException {
		setNodeType(tree.getType());
		setNodeText(tree.getText());
		subType = Expression.createE(getJmlFile(), tree.getFirstChild());
		AST subtree = subType.parse(tree.getFirstChild());
		type = Expression.createE(getJmlFile(), subtree);
		subtree = type.parse(subtree);
		//@ set parsed = true;
		return tree.getNextSibling();
	}

	public LinkInfo linkStatement(IJml2bConfiguration config, LinkContext f)
		throws Jml2bException {
		// link type and subType
		type.linkStatement(config, f);
		// subType (?)
		subType.linkStatement(config, f);

		// it seems that this is a predicate => return a boolean.
		setStateType(Type.getBoolean());
		return new LinkInfo(getStateType());
	}

	public Type typeCheck(IJml2bConfiguration config, LinkContext f)
		throws Jml2bException {
		Type t1 = type.typeCheck(config, f);
		Type t2 = subType.typeCheck(config, f);
		if (t1.getTag() == Type.T_TYPE && t2.getTag() == Type.T_TYPE)
			return Type.getBoolean();
		else
			throw new TypeCheckException(
				"The operator "
					+ getNodeText()
					+ " is undefined for the argument type(s) "
					+ t2.toJava()
					+ ", "
					+ t1.toJava(),
				this);
	}

	public void processIdent() {
		type.processIdent();
		subType.processIdent();
	}

	public void isModifiersCompatible(IJml2bConfiguration config, Modifiers modifiers)
		throws LinkException {
		type.isModifiersCompatible(config, modifiers);
		subType.isModifiersCompatible(config, modifiers);
	}

	public JmlExpression instancie() {
		type = (Expression) type.instancie();
		subType = (Expression) subType.instancie();
		return this;
	}

	public Expression subField(Field f, Field newF) {
		type = type.subField(f, newF);
		subType = subType.subField(f, newF);
		return this;
	}

	public Expression subResult(String ww) {
		type = type.subResult(ww);
		subType = subType.subResult(ww);
		return this;
	}

	public JmlExpression instancie(Expression b) {
		type = (Expression) type.instancie(b);
		subType = (Expression) subType.instancie(b);
		return this;
	}

	public Vector getParsedItems() {
		Vector res = type.getParsedItems();
		res.addAll(subType.getParsedItems());
		res.add((ParsedItem) this);
		return res;
	}

	public void setParsedItem(ParsedItem pi) {
		type.setParsedItem(pi);
		subType.setParsedItem(pi);
		change(pi);
	}

	public boolean isConstant() {
		// return type.isConstant() && subType.isConstant();
		// Return false, since we cannot (yet?) use type values.
		return false;
	}

	//	Vector getFreshVars() {
	//		return new Vector();
	//	}

	public void old() {
		type.old();
		subType.old();
	}

	static final long serialVersionUID = -5719671282257637252L;

	public void getPrecondition(
		IJml2bConfiguration config,
		ModifiableSet modifies,
		Vector req,
		Vector ens) {
	}

	public void collectCalledMethod(Vector calledMethod) {}
	
	/* (non-Javadoc)
	 * @see jml2b.structure.statement.Expression#getFreeVariable(java.util.Set)
	 */
	void getFreeVariable(Set s) {
		subType.getFreeVariable(s);
		type.getFreeVariable(s);
	}

	/**
	 * @return
	 */
	public Expression getSubType() {
		return subType;
	}

	/**
	 * @return
	 */
	public Expression getType() {
		return type;
	}

}
