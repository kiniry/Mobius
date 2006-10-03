//******************************************************************************
/* Copyright (c) 2002, 2003 GEMPLUS Software Research Labs. All Rights Reserved.
/* Copyright (c) 2003, 2004 INRIA. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: WithTypeExp.java
/*
/*******************************************************************************
/* Warnings/Remarks:
/*  09/26/2003 : Simplify integration achieved
/******************************************************************************/
package jml2b.structure.statement;

import java.util.Set;
import java.util.Vector;

import jml2b.IJml2bConfiguration;
import jml2b.exceptions.InternalError;
import jml2b.exceptions.Jml2bException;
import jml2b.exceptions.LinkException;
import jml2b.exceptions.PogException;
import jml2b.exceptions.TypeCheckException;
import jml2b.formula.BinaryForm;
import jml2b.formula.Formula;
import jml2b.formula.IFormToken;
import jml2b.formula.TTypeForm;
import jml2b.formula.TerminalForm;
import jml2b.formula.UnaryForm;
import jml2b.link.LinkContext;
import jml2b.link.LinkInfo;
import jml2b.pog.lemma.FormulaWithPureMethodDecl;
import jml2b.structure.AMethod;
import jml2b.structure.java.AClass;
import jml2b.structure.java.Field;
import jml2b.structure.java.Identifier;
import jml2b.structure.java.JmlFile;
import jml2b.structure.java.Modifiers;
import jml2b.structure.java.ParsedItem;
import jml2b.structure.java.Type;
import jml2b.structure.jml.JmlExpression;
import antlr.collections.AST;

/**
 * This class implements a list of dimension corresponding to an array creation.
 * @author L. Burdy, A. Requet
 **/
class DimExpr extends ParsedItem implements IFormToken {

	/**
	 * The current dimension
	 **/
	/*@ non_null */
	private Expression exp;

	/**
	 * The next element of the list
	 **/
	private DimExpr next;

	/**
	 * Constructs a list as a <i>parsed item</i>.
	 * @param jf The file where the statement is located
	 * @param tree The <code>AST</code> node corresponding to the statement
	 * @see jml2b.structure.java.ParsedItem#ParsedItem(JmlFile, AST)
	 **/
	DimExpr(JmlFile jf, AST tree) throws Jml2bException {
		super(jf, tree);
		exp = Expression.createE(getJmlFile(), tree.getNextSibling());
		AST subtree = exp.parse(tree.getNextSibling());
		if (subtree != null) {
			next = new DimExpr(getJmlFile(), subtree);
		}
	}

	String toJava(int indent) {
		String s = "[" + exp.toJava(indent) + "]";
		if (next != null)
			s += next.toJava(indent);
		return s;
	}

	/**
	 * Tests whether two lists are equal
	 * @return <code>true</code> if the current expressions of the list are 
	 * equal and if the tail of the lists are equal too, <code>false</code> 
	 * otherwise
	 **/
	boolean equals(DimExpr d) {
		return exp.equals(d.exp)
			&& (next == null ? d.next == null : next.equals(d.next));
	}

	LinkInfo linkStatement(IJml2bConfiguration config, LinkContext f)
		throws Jml2bException {
		exp.linkStatement(config, f);
		if (next != null)
			next.linkStatement(config, f);
		return null;
	}

	/**
	 * Collects all the indentifier of the list to give them an index in the 
	 * identifer array. This array is then analyzed to give short name when it
	 * is possible to identifiers.
	 * @see jml2b.pog.IdentifierResolver#bIdents
	 **/
	void processIdent() {
		exp.processIdent();
		if (next != null)
			next.processIdent();
	}

	/**
	 * Returns the set of parsed items that correspond to this list
	 * @return the set of parsed item that correspond to all the expression of  
	 * the list 
	 **/
	Vector getParsedItems() {
		Vector res = exp.getParsedItems();
		if (next != null)
			res.addAll(next.getParsedItems());
		res.add((ParsedItem) this);
		return res;
	}

	public void setParsedItem(ParsedItem pi) {
		exp.setParsedItem(pi);
		if (next != null)
			next.setParsedItem(pi);
		change(pi);
	}

		/**
	 * Returns the next element of the list.
	 * @return <code>next</code>
	 */
	DimExpr getNext() {
		return next;
	}

	static final long serialVersionUID = -1280076634546293684L;

	/**
	 * @return
	 */
	public DimExpr instancie() {
		exp = (Expression) exp.instancie();
		if (next != null)
			next = next.instancie();
		return this;
	}
	/**
	 * @return
	 */
	public Expression getExp() {
		return exp;
	}

}

/**
 * This class implements expression with type, that is object and array
 * creation, casting and <code>instanceof</code>. It contains a type and
 * optionnaly an expression or dimensions for array creation. It corresponds to:
 * <UL>
 * <li> <code>new t(e)</code> the expression is optionnal.
 * <li> <code>new t[e1][e2]...[en]</code>
 * <li> <code>(t) e</code>
 * <li> <code>e instanceof t<code>
 * </UL>
 * @author L. Burdy
 **/
public class WithTypeExp extends Expression {

		/**
	 * Cast a formula into a builtin type.
	 * @param desType The buitlin type in which the formula is casted.
	 * @param srcType The builtin type of the formula
	 * @param f The formula to cast
	 * @return the casted formula that can be itself if the cast does not 
	 * change the formula (for instance byte into int), the j_xxx2yyy funtions 
	 * applicated to the formula if the cast is performed.
	 **/
	private static Formula cast(Type destType, Type srcType, Formula f) {
		switch (destType.getTag()) {
			case Type.T_BOOLEAN :
				return f;
			case Type.T_INT :
				if (srcType.getTag() == Type.T_BYTE
						|| srcType.getTag() == Type.T_SHORT
						|| srcType.getTag() == Type.T_CHAR
						|| srcType.getTag() == Type.T_INT)
				return f;
			case Type.T_LONG :
				if (srcType.getTag() == Type.T_BYTE
						|| srcType.getTag() == Type.T_SHORT
						|| srcType.getTag() == Type.T_CHAR
						|| srcType.getTag() == Type.T_INT
						|| srcType.getTag() == Type.T_LONG)
				return f;
				
			case Type.T_CHAR :
				if (srcType.getTag() == Type.T_CHAR)
					return f;
				else
					return new BinaryForm(
						IFormToken.B_APPLICATION,
						TerminalForm.j_int2char,
						f);

			case Type.T_SHORT :
				if (srcType.getTag() == Type.T_BYTE
					|| srcType.getTag() == Type.T_SHORT)
					return f;
				else
					return new BinaryForm(
						IFormToken.B_APPLICATION,
						TerminalForm.j_int2short,
						f);

			case Type.T_BYTE :
				if (srcType.getTag() == Type.T_BYTE)
					return f;
				else
					return new BinaryForm(
						IFormToken.B_APPLICATION,
						TerminalForm.j_int2byte,
						f);
		}
		throw new jml2b.exceptions.InternalError(
			"WithTypeExp.cast: Impossible cast "
				+ srcType.getTag()
				+ " --> "
				+ destType.getTag());
	}

	/**
	 * Returns the formula corresponding to the default array element 
	 * initializer
	 * @param t The type of the element of the array
	 * @return
	 * <UL>
	 * <li> <code>false</code> for boolean array
	 * <li> <code>0</code> for integer array
	 * <li> <code>null</code> for reference array
	 * </UL>
	 **/
	public static Formula getDefaultArrayInitialiser(Type t) {
		Formula initialiser;
		// get appropriate initialiser 
		switch (t.getTag()) {
			case Type.T_BOOLEAN :
				initialiser = Formula.getFalse();
				break;
			case Type.T_INT :
			case Type.T_SHORT :
			case Type.T_BYTE :
			case Type.T_CHAR :
			case Type.T_LONG :
				initialiser = new TerminalForm(0);
				break;
			case Type.T_DOUBLE :
			case Type.T_FLOAT :
				initialiser = new TerminalForm(0);
				break;
			case Type.T_REF :
			case Type.T_ARRAY :
				initialiser = Formula.getNull();
				break;
			default :
				throw new InternalError(
					"Unhandled case in getDefaultArrayInitialiser: "
						+ t.getTag());
		}
		return initialiser;
	}

	/**
	 * The type used in the expression. It cannot be null.
	 **/
	private Type type;

	/*@
	  @ invariant parsed ==> type != null;
	  @*/

	/**
	 * The expression can be
	 * <UL>
	 * <li> the parameter of a constructor call
	 * <li> an array intialiazer
	 * <li> a casted expression
	 * <li> a tested with <code>instanceof</code> expression
	 * </UL>
	 **/
	private Expression exp;

	/**
	 * The dimensions of created arrays.
	 **/
	private DimExpr dim;

	/**
	 * The identifier corresponding to the called constructor. It is only valid
	 * for an object created and is evaluated during the link.
	 **/
	private Identifier ident;

	/**
	 * Constructs an expression as a <i>parsed item</i>.
	 * @param jf The file where the statement is located
	 * @param tree The <code>AST</code> node corresponding to the statement
	 * @see jml2b.structure.java.ParsedItem#ParsedItem(JmlFile, AST)
	 **/
	protected WithTypeExp(JmlFile jf, AST tree) {
		super(jf, tree);
	}

	/**
	 * Constructs an expression with type form another expression with type.
	 * @param nodeType The node type
	 * @param nodeText The node text
	 * @param type The type corresponding to this expression
	 * @param exp The sub expression
	 **/
	/*@
	  @ requires exp != null;
	  @*/
	WithTypeExp(int nodeType, String nodeText, Type type, Expression exp) {
		super(nodeType, nodeText);
		this.type = type;
		this.exp = exp;
		//@ set parsed = true;
	}

	public Object clone() {
		WithTypeExp res =
			new WithTypeExp(
				getNodeType(),
				getNodeText(),
				type,
				exp == null ? null : (Expression) exp.clone());
		res.setBox(this);
		res.setStateType(getStateType());
		return res;
	}

	public boolean equals(Expression e) {
		return getNodeType() == e.getNodeType()
			&& type.equals(((WithTypeExp) e).type)
			&& (exp == null
				? ((WithTypeExp) e).exp == null
				: (((WithTypeExp) e).exp != null
					&& exp.equals(((WithTypeExp) e).exp)))
			&& (dim == null
				? ((WithTypeExp) e).dim == null
				: (((WithTypeExp) e).dim != null
					&& dim.equals(((WithTypeExp) e).dim)))
			&& (ident == null
				? ((WithTypeExp) e).ident == null
				: (((WithTypeExp) e).ident != null
					&& ident.equals(((WithTypeExp) e).ident)));
	}

	/**
	 * Object and array creations are not converted. 
	 * <code>(yyy) e</code> is converted in <code>j_xxx2yyy</code> when yyy is a
	 * builtin type.
	 * <code>(yyy) e</code> is converted in <code>e</code> otherwise.
	 * <code>e instanceof t</code> is converted into 
	 * <code>typeof(e) <: \type(t)</code>
	 **/
	FormulaWithPureMethodDecl exprToContextForm(
		IJml2bConfiguration config,
		Vector methods,
		boolean pred)
		throws Jml2bException, PogException {
		Formula res;
		FormulaWithPureMethodDecl c = exp.exprToContextForm(config, methods, false);
		switch (getNodeType()) {
			case CAST :
				if (type.isBuiltin())
					res = cast(type, exp.getStateType(), c.getFormula());
				else
					res = c.getFormula();
				break;
			case LITERAL_instanceof :
				res =
					new UnaryForm(
						B_BOOL,
						new BinaryForm(
							Jm_IS_SUBTYPE,
							new BinaryForm(
								IFormToken.B_APPLICATION,
								TerminalForm.typeof,
								c.getFormula()),
							new TTypeForm(IFormToken.Jm_T_TYPE, type)));
				break;
			default :
				return null;
		}
		return new FormulaWithPureMethodDecl(c, res);
	}

	public String toJava(int indent) {
		switch (getNodeType()) {
			case CAST :
				return "(" + type.toJava() + ") (" + exp.toJava(indent) + ")";
			case LITERAL_instanceof :
				return exp.toJava(indent) + " instanceof " + type.toJava();
			case NEWARRAY :
				if (dim == null)
					return "new " + type.toJava() + exp.toJava(indent);
				else
					return "new " + type.toJava() + dim.toJava(indent);
			case LITERAL_new :
				return "new "
					+ type.toJava()
					+ "("
					+ (exp != null ? exp.toJava(indent) : "")
					+ ")";
			default :
				return "";
		}
	}

	public AST parse(AST tree) throws Jml2bException {
		//@ set parsed = true;
		AST subtree;
		setNodeType(tree.getType());
		setNodeText(tree.getText());
		switch (getNodeType()) {
			case CAST :
				type = new Type(getJmlFile(), tree.getFirstChild());
				subtree = type.parse(tree.getFirstChild());
				exp = Expression.createE(getJmlFile(), subtree);
				exp.parse(subtree);
				break;
			case LITERAL_instanceof :
				exp = Expression.createE(getJmlFile(), tree.getFirstChild());
				subtree = exp.parse(tree.getFirstChild());
				type =
					new Type(
						getJmlFile(),
						tree.getFirstChild().getNextSibling());
				type.parse(tree.getFirstChild().getNextSibling());
				break;
			case LITERAL_new :
				type = new Type(getJmlFile(), tree.getFirstChild());
				subtree = type.parse(tree.getFirstChild());
				if (subtree != null) {
					if (subtree.getType() == DIM_EXPRS) {
						setNodeType(NEWARRAY);
						dim =
							new DimExpr(getJmlFile(), subtree.getFirstChild());
						if (subtree.getNextSibling() != null) {
							type =
								Type.addDims(
									getJmlFile(),
									subtree.getNextSibling(),
									type);
						}
					} else if (subtree.getType() == LCURLY) {
						setNodeType(NEWARRAY);
						exp = Expression.createE(getJmlFile(), subtree);
						subtree = exp.parse(subtree);
					} else {
						exp = Expression.createE(getJmlFile(), subtree);
						subtree = exp.parse(subtree);
					}
				}
				break;
			default :
				throw new Jml2bException("");
		}
		return tree.getNextSibling();
	}

	public LinkInfo linkStatement(IJml2bConfiguration config, LinkContext f)
		throws Jml2bException {
		switch (getNodeType()) {
			case LITERAL_new :
				{
					Vector parameters = new Vector();
					// link the type
					type.link(config, f);

					setStateType(type);

					if (exp != null) {
						// link parameters
						exp.linkParameters(config, f, parameters);
					}

					AClass c = type.getRefType();

					if (c == null) {
						throw new LinkException(
							"Found constructor for " + "non-reference type",
							this);
					}

					AMethod ctor = c.getConstructor(config, parameters);

					if (ctor == null) {
						throw new LinkException(
							"Cannot find constructor for "
								+ "class "
								+ c.getName()
								+ " with paramaters "
								+ Type.signatureToString(parameters.elements()),
							this);
					}

					ident = new Identifier(ctor);

					break;
				}
			case NEWARRAY :
				{
					// link the type
					type.link(config, f);

					if (dim == null) {
						setStateType(type);
						exp.linkStatement(config, f);
					} else {
						Type tmp = type;
						// add dimensions corresponding to the DIM_EXPRS statements
						DimExpr current = dim;
						while (current != null) {
							// add an array dimension
							tmp = new Type(config, tmp);
							// go to the next DIM_EXPRS statement
							current = current.getNext();
						}
						setStateType(tmp);
						// link the DIM_EXPRS statements
						dim.linkStatement(config, f);
					}
					break;
				}
			case LITERAL_instanceof :
				type.link(config, f);
				setStateType(Type.getBoolean());
				exp.linkStatement(config, f);
				// return a boolean type
				break;

				// same as instanceof, but return the type instead of a 
				// boolean
			case CAST :
				type.link(config, f);
				setStateType(type);

				exp.linkStatement(config, f);
				// return the type corresponding to the cast
				break;
		}
		return new LinkInfo(getStateType());
	}

	public Type typeCheck(IJml2bConfiguration config, LinkContext f)
		throws Jml2bException {
		switch (getNodeType()) {
			case LITERAL_new :
			case NEWARRAY :
				return null;
			case LITERAL_instanceof :
				{
					Type t = exp.typeCheck(config, f);
					if (t.isRef())
						return Type.getBoolean();
					else
						throw new TypeCheckException(
							"Incompatible conditional operand types "
								+ t.toJava()
								+ " and ?"
								+ type.toJava(),
							this);
				}
			case CAST :
				Type t = exp.typeCheck(config, f);
				if (t.isRef() && type.isRef())
					return type; //TODO Completer les test du cast
				if (t.isNumeric() && type.isNumeric())
					return type;
				if (t.isBoolean() && type.isBoolean())
					return type;
				if (t.getTag() == Type.T_TYPE && type.getTag() == Type.T_TYPE)
					return type;
				throw new TypeCheckException(
					"Cannot cast from " + t.toJava() + " to ?" + type.toJava(),
					this);
		}
		return null;
	}

	public void processIdent() {
		if (exp != null)
			exp.processIdent();
		if (dim != null)
			dim.processIdent();
	}

	public void isModifiersCompatible(IJml2bConfiguration config, Modifiers modifiers)
		throws LinkException {
		if (exp != null)
			exp.isModifiersCompatible(config, modifiers);
		//        if (dim != null)
		//            dim.isModifiersCompatible(modifiers);
	}

	public JmlExpression instancie() {
		if (exp != null)
			exp = (Expression) exp.instancie();
		if (dim != null)
			dim = dim.instancie();
		return this;
	}

	public Expression subField(Field f, Field newF) {
		exp = (exp == null ? null : exp.subField(f, newF));
		return this;
	}

	public Expression subResult(String ww) {
		exp = (exp == null ? null : exp.subResult(ww));
		return this;
	}

	public Vector getParsedItems() {
		Vector res = new Vector();
		res.add((ParsedItem) type);
		if (exp != null)
			res.addAll(exp.getParsedItems());
		if (dim != null)
			res.addAll(dim.getParsedItems());
		res.add((ParsedItem) this);
		return res;
	}

	public void setParsedItem(ParsedItem pi) {
		type.setParsedItem(pi);
		if (exp != null)
			exp.setParsedItem(pi);
		if (dim != null)
			dim.setParsedItem(pi);
		change(pi);
	}

	//	Vector getFreshVars() {
	//		return new Vector();
	//	}

	public void old() {
		if (exp != null)
			exp.old();
	}

	public JmlExpression instancie(Expression b) {
		exp = (exp == null ? null : (Expression) exp.instancie(b));
		return this;
	}

	public boolean isConstant() {
		switch (getNodeType()) {
			case CAST :
				switch (type.getTag()) {
					case Type.T_INT :
					case Type.T_SHORT :
					case Type.T_CHAR :
					case Type.T_BYTE :
						return exp.isConstant();
				}
			default :
				return false;
		}
	}

	public int getValue() {
		switch (getNodeType()) {
			case CAST :
				switch (type.getTag()) {
					case Type.T_INT :
						return exp.getValue();
					case Type.T_SHORT :
						return (short) exp.getValue();
					case Type.T_CHAR :
						return (char) exp.getValue();
					case Type.T_BYTE :
						return (byte) exp.getValue();
				}
			default :
				throw new jml2b.exceptions.InternalError(
					"WithTypeExp.getValue() called for non-constant expression");
		}
	}

	public void collectCalledMethod(Vector calledMethod) {
		if (exp != null)
			exp.collectCalledMethod(calledMethod);
		if (dim != null) {
			DimExpr le = dim;
			while (le != null) {
				le.getExp().collectCalledMethod(calledMethod);
				le = le.getNext();
			}
		}
	}
	static final long serialVersionUID = -7901462666342789890L;

	/* (non-Javadoc)
	 * @see jml2b.structure.statement.Expression#getFreeVariable(java.util.Set)
	 */
	void getFreeVariable(Set s) {
		if (exp != null)
			exp.getFreeVariable(s);
		if (dim != null) {
			DimExpr le = dim;
			while (le != null) {
				le.getExp().getFreeVariable(s);
				le = le.getNext();
			}
		}
	}

	/**
	 * @return
	 */
	public Expression getExp() {
		return exp;
	}

	/**
	 * @return
	 */
	public Type getType() {
		return type;
	}

}