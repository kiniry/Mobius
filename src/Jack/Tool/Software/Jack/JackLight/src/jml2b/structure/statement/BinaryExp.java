//******************************************************************************
/* Copyright (c) 2002, 2003 GEMPLUS Software Research Labs. All Rights Reserved.
 /* Copyright (c) 2003, 2004 INRIA. All Rights Reserved.
 /*------------------------------------------------------------------------------
 /* Name: BinaryExp
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
import jml2b.formula.ElementsForm;
import jml2b.formula.Formula;
import jml2b.formula.IFormToken;
import jml2b.formula.TerminalForm;
import jml2b.formula.UnaryForm;
import jml2b.link.LinkContext;
import jml2b.link.LinkInfo;
import jml2b.pog.lemma.FormulaWithPureMethodDecl;
import jml2b.structure.java.Field;
import jml2b.structure.java.Identifier;
import jml2b.structure.java.JavaLoader;
import jml2b.structure.java.JmlFile;
import jml2b.structure.java.Modifiers;
import jml2b.structure.java.ParsedItem;
import jml2b.structure.java.Type;
import jml2b.structure.jml.JmlExpression;
import antlr.collections.AST;

/**
 * This class implements binary expressions. Java binary expressions can be:
 * <UL>
 * <li>a.b
 * <li>a,b
 * <li>a + b
 * <li>a - b
 * <li>a * b
 * <li>a / b
 * <li>a % b
 * <li>a < < b
 * <li>a >> b
 * <li>a >>> b
 * <li>a & b
 * <li>a | b
 * <li>a ^ b
 * <li>a = b
 * <li>a < <= b
 * <li>a >>= b
 * <li>a >>>= b
 * <li>a &= b
 * <li>a |= b
 * <li>a ^= b
 * <li>a += b
 * <li>a -= b
 * <li>a *= b
 * <li>a /= b
 * <li>a %= b
 * <li>a == b
 * <li>a != b
 * <li>a && b
 * <li>a || b
 * <li>a <= b
 * <li>a < b
 * <li>a >= b
 * <li>a > b
 * <li>a[b]
 * </UL>
 * Jml binary expressions can be:
 * <UL>
 * <li>a ==> b
 * </UL>
 * 
 * @author L. Burdy, A. Requet
 */
public class BinaryExp extends Expression {

	/**
	 * Returns the B function associated to a Java operator
	 * 
	 * @param s
	 *                    The Java operator
	 * @return The associated <code>j_xxx</code> function :
	 *                <UL>
	 *                <li>j_shl for < <
	 *                <li>j_shr for >>
	 *                <li>j_ushr for >>>
	 *                <li>j_and for &
	 *                <li>j_or for |
	 *                <li>j_xor for ^
	 *                </UL>
	 */
	private static String getJFunction(String s) {
		if (s.equals("<<"))
			return "j_shl";
		else if (s.equals(">>"))
			return "j_shr";
		else if (s.equals(">>>"))
			return "j_ushr";
		else if (s.equals("&"))
			return "j_and";
		else if (s.equals("|"))
			return "j_or";
		else if (s.equals("^"))
			return "j_xor";
		throw new InternalError("BinaryExp.getJFunction: unknown operator " + s);
	}

	/**
	 * The left expression
	 */
	private Expression left;

	/**
	 * The right expression.
	 */
	private Expression right;

	/*
	 * @ @ invariant parsed ==> left != null @ && parsed ==> right != null @ &&
	 * parsed ==> left.parsed @ && parsed ==> right.parsed; @
	 */

	/**
	 * Constructs an expression as a <i>parsed item </i>.
	 * 
	 * @param jf
	 *                    The file where the statement is located
	 * @param tree
	 *                    The <code>AST</code> node corresponding to the statement
	 * @see jml2b.structure.java.ParsedItem#ParsedItem(JmlFile, AST)
	 */
	BinaryExp(JmlFile jf, AST tree) {
		super(jf, tree);
	}

	/**
	 * Constructs a quantified expression form another one
	 * 
	 * @param nodeType
	 *                    The node type
	 * @param nodeText
	 *                    The node text
	 * @param left
	 *                    The left expression
	 * @param right
	 *                    The right expression
	 */
	/*
	 * @ @ requires left != null && right != null; @
	 */
	public BinaryExp(int nodeType, Expression left, String nodeText, Expression right) {
		super(nodeType, nodeText);
		this.left = left;
		this.right = right;
		//@ set parsed = true;
	}

	public Object clone() {
		BinaryExp res = new BinaryExp(getNodeType(), (Expression) left.clone(), getNodeText(), (Expression) right
				.clone());
		res.setBox(this);
		res.setStateType(getStateType());
		return res;
	}

	public boolean equals(Expression e) {
		return getNodeType() == e.getNodeType() && left.equals(((BinaryExp) e).left)
				&& right.equals(((BinaryExp) e).right);
	}

	/**
	 * Converts the expression in a formula with a context issue from the pure
	 * method call.
	 * <UL>
	 * <li><code>a.b</code> is converted in <code>b</code> if b is a static
	 * field, in <code>b(a)</code> otherwise
	 * <li><code>a,b</code> is converted identically
	 * <li><code>a + b</code> is converted identically
	 * <li><code>a - b</code> is converted identically
	 * <li><code>a * b</code> is converted identically
	 * <li><code>a / b</code> is converted identically
	 * <li><code>a % b</code> is converted identically
	 * <li><code>a << b</code> is converted in <code>j_shl(a,b)</code>
	 * <li><code>a >> b</code> is converted in <code>j_shr(a,b)</code>
	 * <li><code>a >>> b</code> is converted in <code>j_ushr(a,b)</code>
	 * <li><code>a & b</code> is converted in <code>j_and(a,b)</code>
	 * <li><code>a | b</code> is converted in <code>j_or(a,b)</code>
	 * <li><code>a ^ b</code> is converted in <code>j_xor(a,b)</code>
	 * <li><code>a = b</code> is not converted
	 * <li><code>a <<= b</code> is not converted
	 * <li><code>a >>= b</code> is not converted
	 * <li><code>a >>>= b</code> is not converted
	 * <li><code>a &= b</code> is not converted
	 * <li><code>a |= b</code> is not converted
	 * <li><code>a ^= b</code> is not converted
	 * <li><code>a += b</code> is not converted
	 * <li><code>a -= b</code> is not converted
	 * <li><code>a *= b</code> is not converted
	 * <li><code>a /= b</code> is not converted
	 * <li><code>a %= b</code> is not converted
	 * <li><code>a == b</code> is converted identically
	 * <li><code>a != b</code> is converted identically
	 * <li><code>a && b</code> is converted identically
	 * <li><code>a || b</code> is converted identically
	 * <li><code>a <= b</code> is converted identically
	 * <li><code>a < b</code> is converted identically
	 * <li><code>a >= b</code> is converted identically
	 * <li><code>a > b</code> is converted identically
	 * <li><code>a[b]</code> is converted in <code>xxxelements(a)(b)</code>
	 * <li><code>a ==> b</code> is converted identically
	 * </UL>
	 */
	FormulaWithPureMethodDecl exprToContextForm(IJml2bConfiguration config, Vector methods, boolean pred)
			throws Jml2bException, PogException {
		FormulaWithPureMethodDecl r, l;
		switch (getNodeType()) {
			case LOGICAL_OP :
			case IMPLICATION_OP :
				r = right.exprToContextForm(config, methods, true);
				l = left.exprToContextForm(config, methods, true);
				break;
			case BITWISE_OP :
				if (left.getStateType().isBoolean()) {
					r = right.exprToContextForm(config, methods, true);
					l = left.exprToContextForm(config, methods, true);
					break;
				}
			default :
				r = right.exprToContextForm(config, methods, false);
				l = left.exprToContextForm(config, methods, false);
				break;
		}

		Formula res;
		switch (getNodeType()) {
			case DOT :
				if (right.getNodeType() == IDENT) {
					if (((TerminalExp) right).getIdent() == null)
						return right.exprToContextForm(config, methods, pred);
					switch (((TerminalExp) right).getIdent().idType) {
						case Identifier.ID_CLASS :
						case Identifier.ID_PACKAGE :
							return r;
						case Identifier.ID_FIELD :
							if (((TerminalExp) right).getIdent().field.getModifiers().isStatic())
								return right.exprToContextForm(config, methods, pred);
							else {
								res = new BinaryForm(IFormToken.B_APPLICATION, r.getFormula(), l.getFormula());
								if (pred)
									res = new BinaryForm(Ja_EQUALS_OP, res, new TerminalForm(Ja_LITERAL_true));
								return new FormulaWithPureMethodDecl(r, l, res);
							}
						case Identifier.ID_METHOD :
							throw new InternalError("BinaryExp.exprToForm : bad idType in DOT "
													+ ((TerminalExp) right).getIdent().idType);
					}
				} else {
					throw new InternalError("BinaryExp.exprToForm : bad node type in DOT " + right.getNodeType());
				}
			case LBRACK :
				if (right.getNodeType() == STAR_ELEMS)
				{
					res = new BinaryForm(IFormToken.ALL_ARRAY_ELEMS, ElementsForm
										.getElementsName(left.getStateType().getElemType()), l.getFormula());
					if (pred)
						res = new BinaryForm(Ja_EQUALS_OP, res, new TerminalForm(Ja_LITERAL_true));

					return new FormulaWithPureMethodDecl(l, res);
				}
				
				else {
				res = new BinaryForm(IFormToken.ARRAY_ACCESS, new BinaryForm(IFormToken.B_APPLICATION, ElementsForm
						.getElementsName(left.getStateType().getElemType()), l.getFormula()), r.getFormula());
				if (pred)
					res = new BinaryForm(Ja_EQUALS_OP, res, new TerminalForm(Ja_LITERAL_true));

				return new FormulaWithPureMethodDecl(r, l, res);
				}
			case BITWISE_OP :
				if (left.getStateType().isBoolean()) {
					byte token = 0;
					if (getNodeText().equals("|")) {
						token = IFormToken.Ja_OR_OP;
					} else if (getNodeText().equals("&")) {
						token = IFormToken.Ja_AND_OP;
					} else if (getNodeText().equals("^")) {
						token = IFormToken.Ja_DIFFERENT_OP;
					} else
						throw new jml2b.exceptions.InternalError("Unknown BITWISE_OP: " + getNodeText());
					res = new BinaryForm(token, l.getFormula(), r.getFormula());
					if (!pred)
						res = new UnaryForm(B_BOOL, res);
					return new FormulaWithPureMethodDecl(r, l, res);
				}
			case SHIFT_OP :
				res = new BinaryForm(IFormToken.B_APPLICATION, new TerminalForm(getJFunction(getNodeText())),
						new BinaryForm(Ja_COMMA, l.getFormula(), r.getFormula()));
				return new FormulaWithPureMethodDecl(r, l, res);
			case LOGICAL_OP :
					res = new BinaryForm((getNodeText().equals("&&") ? Ja_AND_OP : Ja_OR_OP), l.getFormula(), r
							.getFormula());
					if (!pred) 
					res = new UnaryForm(B_BOOL, res);
					return new FormulaWithPureMethodDecl(l, r, res);
//				} else {
//					return new FormulaWithPureMethodDecl(new BinaryForm(
//							(getNodeText().equals("&&") ? Ja_AND_OP : Ja_OR_OP), l.getFormulaWithContext(), r
//									.getFormulaWithContext()));
//			}
			case IMPLICATION_OP :
					res = new BinaryForm(Jm_IMPLICATION_OP, l.getFormula(), r.getFormula());
					if (!pred) 
					res = new UnaryForm(B_BOOL, res);
					return new FormulaWithPureMethodDecl(l, r, res);
//				} else {
//					return new ContextFromPureMethod(l, new BinaryForm(Jm_IMPLICATION_OP, l.getFormula(), r
//							.getFormulaWithContext()));
//				}
			default :
				byte n = -1;
				switch (getNodeType()) {
					case COMMA :
						n = Ja_COMMA;
						break;
					case ADDITIVE_OP :
						if (getNodeText().equals("+"))
							n = Ja_ADD_OP;
						else
							n = Ja_NEGATIVE_OP;
						break;
					case MULTIPLICATIVE_OP :
						if (getNodeText().equals("*"))
							n = Ja_MUL_OP;
						else if (getNodeText().equals("%"))
							n = Ja_MOD;
						else
							n = Ja_DIV_OP;
						res = new BinaryForm(n, l.getFormula(), r.getFormula());
						break;
					case RELATIONAL_OP :
						if (getNodeText().equals("<="))
							n = Ja_LE_OP;
						else if (getNodeText().equals("<"))
							n = Ja_LESS_OP;
						else if (getNodeText().equals(">="))
							n = Ja_GE_OP;
						else
							n = Ja_GREATER_OP;
						res = new BinaryForm(n, l.getFormula(), r.getFormula());
						if (!pred)
							res = new UnaryForm(B_BOOL, res);
						return new FormulaWithPureMethodDecl(r, l, res);
					case EQUALITY_OP :
						if (getNodeText().equals("=="))
							n = Ja_EQUALS_OP;
						else
							n = Ja_DIFFERENT_OP;
						res = new BinaryForm(n, l.getFormula(), r.getFormula());
						if (!pred)
							res = new UnaryForm(B_BOOL, res);
						return new FormulaWithPureMethodDecl(r, l, res);
					default :
						throw new InternalError("BinaryExp.exprToForm : bad node type  "
												+ MyToken.nodeString[getNodeType()] + " (" + getNodeType() + ")");
				}
				res = new BinaryForm(n, l.getFormula(), r.getFormula());
				return new FormulaWithPureMethodDecl(r, l, res);
		}
	}

	public String toJava(int indent) {
		String r = left.toJava(indent);
		switch (getNodeType()) {
			case LBRACK :
				return r + "[" + right.toJava(indent + r.length() + 1) + "]";
			case LOGICAL_OP :
				return r + getNodeText() + "\n" + Expression.indent(indent) + right.toJava(indent);
			case DOT :
			case COMMA :
			case SHIFT_OP :
			case ADDITIVE_OP :
			case MULTIPLICATIVE_OP :
			case BITWISE_OP :
			case RELATIONAL_OP :
			case IMPLICATION_OP :
			case ASSIGN :
			case EQUALITY_OP :
			case BITWISE_ASSIGNMENT_OP :
			case ADDITIVE_ASSIGNMENT_OP :
			case MULTIPLICATIVE_ASSIGNMENT_OP :
			case SHIFT_ASSIGNMENT_OP :
				if (Expression.getPriority(left.getNodeType()) < Expression.getPriority(getNodeType()))
					r = "(" + r + ")";
				String rs = right.toJava(indent + r.length() + getNodeText().length());
			if (Expression.getPriority(right.getNodeType()) <= Expression.getPriority(getNodeType()))
					rs = "(" + rs + ")";
				return r + getNodeText() + rs;
			default :
				return "";
		}
	}

	public AST parse(AST tree) throws Jml2bException {
		//@ set parsed = true;
		AST parsedTree = null;
		if (tree.getType() == SET)
			parsedTree = tree.getFirstChild();
		else
			parsedTree = tree;
		setNodeType(parsedTree.getType());
		setNodeText(parsedTree.getText());
		left = Expression.createE(getJmlFile(), parsedTree.getFirstChild());
		left.parse(parsedTree.getFirstChild());
		right = Expression.createE(getJmlFile(), parsedTree.getFirstChild().getNextSibling());
		right.parse(parsedTree.getFirstChild().getNextSibling());
		return tree.getNextSibling();
	}

	public LinkInfo linkStatement(IJml2bConfiguration config, LinkContext f) throws Jml2bException {
		switch (getNodeType()) {
			case COMMA :
				left.linkStatement(config, f);
				return right.linkStatement(config, f);
			case SHIFT_ASSIGNMENT_OP :
			case BITWISE_ASSIGNMENT_OP :
			case ADDITIVE_ASSIGNMENT_OP :
			case MULTIPLICATIVE_ASSIGNMENT_OP : {
				// the type of those assignment is the type of the left
				// node
				LinkInfo res = left.linkStatement(config, f);

				// attention, il doit y avoir des conversions de type
				// ? ajouter.
				right.linkStatement(config, f);

				setStateType(res.getType());
				return res;
			}

			case BITWISE_OP : {
				// attention, il doit y avoir des conversions de type
				// ? ajouter.
				LinkInfo l = left.linkStatement(config, f);
				LinkInfo r = right.linkStatement(config, f);
				Type l_t = l.getType();
				Type r_t = l.getType();

				if (l_t.getTag() == Type.T_BOOLEAN) {
					setStateType(l_t);
					return l;
				} else {
					// in this case, we should have two builtin types.
					// the type of the result is equal to int
					setStateType(Type.getInteger());

					// try to reuse an existing LinkInfo instead of creating
					// a new one.
					if (r_t.getTag() == Type.T_INT) {
						return r;
					}
					if (l_t.getTag() == Type.T_INT) {
						return l;
					}
					return new LinkInfo(getStateType());
				}
			}
			case SHIFT_OP :
			case ADDITIVE_OP :
			case MULTIPLICATIVE_OP : {
				// attention, il doit y avoir des conversions de type
				// ? ajouter.
				LinkInfo l = left.linkStatement(config, f);
				LinkInfo r = right.linkStatement(config, f);
				Type l_t = l.getType();
				Type r_t = l.getType();

				// in case where one of the side is of type reference, it is
				// assumed that it is a String, and that the result is also
				// a String => return the reference one.
				if (l_t.getTag() == Type.T_REF) {
					setStateType(l_t);
					return l;
				} else if (r_t.getTag() == Type.T_REF) {
					setStateType(r_t);
					return r;
				} else {
					// in this case, we should have two builtin types.
					// the type of the result is equal to int
					setStateType(Type.getInteger());

					// try to reuse an existing LinkInfo instead of creating
					// a new one.
					if (r_t.getTag() == Type.T_INT) {
						return r;
					}
					if (l_t.getTag() == Type.T_INT) {
						return l;
					}
					return new LinkInfo(getStateType());
				}
			}

			case EQUALITY_OP :
			case LOGICAL_OP :
			case RELATIONAL_OP :
			case IMPLICATION_OP :
				// operations on boolean values
				setStateType(Type.getBoolean());
				left.linkStatement(config, f);
				right.linkStatement(config, f);
				return new LinkInfo(getStateType());
			case LBRACK : {
				LinkInfo res = left.linkStatement(config, f);
				right.linkStatement(config, f);

				if (res.tag == LinkInfo.TYPE) {
					setStateType(res.getType().getElemType());
					return new LinkInfo(getStateType());
				}
				break;
			}
			case ASSIGN : {
				LinkInfo res = left.linkStatement(config, f);
				right.linkStatement(config, f);
				setStateType(res.getType());
				return res;
			}
			case DOT : {
				// Statement left
				LinkInfo lft = left.linkStatement(config, f);
				LinkContext l = new LinkContext(f, lft);
				// 
				// Statement right
				LinkInfo res = right.linkStatement(config, l);
				setStateType(res.getType());

				return res;
			}
			default :
				throw new InternalError("Don't know how to link " + MyToken.nodeString[getNodeType()]);
		}
		return null;
	}

	public Type typeCheck(IJml2bConfiguration config, LinkContext f) throws Jml2bException {
		switch (getNodeType()) {
			case COMMA :
				left.typeCheck(config, f);
				right.typeCheck(config, f);
				return null;
			case ASSIGN :
			case SHIFT_ASSIGNMENT_OP :
			case BITWISE_ASSIGNMENT_OP :
			case ADDITIVE_ASSIGNMENT_OP :
			case MULTIPLICATIVE_ASSIGNMENT_OP :
				return null;

			case SHIFT_OP : {
				Type t1 = left.typeCheck(config, f);
				Type t2 = right.typeCheck(config, f);
				if (t1.isIntegral() && t2.isIntegral())
					return t1.unaryPromote();
				else
					throw new TypeCheckException("The operator " + getNodeText()
													+ " is undefined for the argument type(s) " + t1.toJava() + ", "
													+ t2.toJava(), this);
			}
			case BITWISE_OP : {
				Type t1 = left.typeCheck(config, f);
				Type t2 = right.typeCheck(config, f);
				if (t1.isIntegral() && t2.isIntegral())
					return Type.binaryNumericPromotion(t1, t2);
				else if (t1.isBoolean() && t2.isBoolean())
					return t1;
				else
					throw new TypeCheckException("The operator " + getNodeText()
													+ " is undefined for the argument type(s) " + t1.toJava() + ", "
													+ t2.toJava(), this);
			}
			case MULTIPLICATIVE_OP : {
				Type t1 = left.typeCheck(config, f);
				Type t2 = right.typeCheck(config, f);
				if (t1.isIntegral() && t2.isIntegral())
					return Type.binaryNumericPromotion(t1, t2);
				else
					throw new TypeCheckException("The operator " + getNodeText()
													+ " is undefined for the argument type(s) " + t1.toJava() + ", "
													+ t2.toJava(), this);
			}
			case ADDITIVE_OP : {
				Type t1 = left.typeCheck(config, f);
				Type t2 = right.typeCheck(config, f);
				if (getNodeText().equals("+")) {
					if (t1.getTag() == Type.T_REF && t1.getRefType() == ((JavaLoader) config.getPackage()).getJavaLang().getClass("String"))
						return t1;
					if (t2.getTag() == Type.T_REF && t2.getRefType() == ((JavaLoader) config.getPackage()).getJavaLang().getClass("String"))
						return t2;
				}
				if (t1.isIntegral() && t2.isIntegral())
					return Type.binaryNumericPromotion(t1, t2);
				else
					throw new TypeCheckException("The operator " + getNodeText()
													+ " is undefined for the argument type(s) " + t1.toJava() + ", "
													+ t2.toJava(), this);
			}
			case EQUALITY_OP : {
				Type t1 = left.typeCheck(config, f);
				Type t2 = right.typeCheck(config, f);
				if (t1.isIntegral() && t2.isIntegral())
					return Type.getBoolean();
				else if (t1.isBoolean() && t2.isBoolean())
					return t1;
				else if (t1.isRef() && t2.isRef())
					return Type.getBoolean();
				else if (t1.getTag() == Type.T_TYPE && t2.getTag() == Type.T_TYPE)
					return Type.getBoolean();
				else
					throw new TypeCheckException("The operator " + getNodeText()
													+ " is undefined for the argument type(s) " + t1.toJava() + ", "
													+ t2.toJava(), this);
			}
			case LOGICAL_OP :
			case IMPLICATION_OP : {
				Type t1 = left.typeCheck(config, f);
				Type t2 = right.typeCheck(config, f);
				if (t1.isBoolean() && t2.isBoolean())
					return t1;
				else
					throw new TypeCheckException("The operator " + getNodeText()
													+ " is undefined for the argument type(s) " + t1.toJava() + ", "
													+ t2.toJava(), this);
			}
			case RELATIONAL_OP : {
				Type t1 = left.typeCheck(config, f);
				Type t2 = right.typeCheck(config, f);
				if (t1.isNumeric() && t2.isNumeric())
					return Type.getBoolean();
				else
					throw new TypeCheckException("The operator " + getNodeText()
													+ " is undefined for the argument type(s) " + t1.toJava() + ", "
													+ t2.toJava(), this);
			}
			case LBRACK : {
				Type t1 = left.typeCheck(config, f);
				Type t2 = right.typeCheck(config, f);
				if (t1.getTag() != Type.T_ARRAY)
					throw new TypeCheckException("The type of the expression must be an array type "
													+ "but it resolved to " + t1.toJava(), this);
				else if (t2.isIntegral())
					return t1.getElemType();
				else
					throw new TypeCheckException("Type mismatch: cannot convert from " + t1.toJava() + " to int", this);
			}
			case DOT : {
				// Statement left
				left.typeCheck(config, f);
				right.typeCheck(config, f);

				return getStateType();
			}
			default :
				throw new InternalError("Don't know how to type check " + MyToken.nodeString[getNodeType()]);
		}
	}

	public void processIdent() {
		left.processIdent();
		right.processIdent();
	}

	public void isModifiersCompatible(IJml2bConfiguration config, Modifiers modifiers) throws LinkException {
		if (getNodeType() == DOT) {
			left.isModifiersCompatible(config, modifiers);
		} else {
			left.isModifiersCompatible(config, modifiers);
			right.isModifiersCompatible(config, modifiers);
		}
	}

	public JmlExpression instancie() {
		if (getNodeType() == DOT) {
			Identifier i = ((TerminalExp) right).getIdent();
			if (i == null) {
				left = (Expression) left.instancie();
			} else
				switch (i.idType) {
					case Identifier.ID_FIELD :
						if (i.field.isLocal() || i.field.getModifiers().isStatic()) {
							right.change(getParsedItems());
							return right;
						}
						left = (Expression) left.instancie();
						break;
					case Identifier.ID_METHOD :
						if (i.mth.getModifiers().isStatic()) {
							return right;
						}
						left = (Expression) left.instancie();
						break;
					default :
						throw new jml2b.exceptions.InternalError("Don't know how to instancie : "
																	+ nodeString[getNodeType()] + " with ident "
																	+ i.getName() + " of type " + i.idType);
				}
		} else {
			left = (Expression) left.instancie();
			right = (Expression) right.instancie();
		}
		return this;
	}

	public JmlExpression instancie(Expression b) {
		left = (Expression) left.instancie(b);
		right = (Expression) right.instancie(b);
		return this;
	}

	public Expression subField(Field f, Field newF) {
		left = left.subField(f, newF);
		right = right.subField(f, newF);
		return this;
	}

	public Expression subResult(String ww) {
		left = left.subResult(ww);
		right = right.subResult(ww);
		return this;
	}

	public Vector getParsedItems() {
		Vector res = left.getParsedItems();
		res.addAll(right.getParsedItems());
		res.add((ParsedItem) this);
		return res;
	}

	public void setParsedItem(ParsedItem pi) {
		left.setParsedItem(pi);
		right.setParsedItem(pi);
		change(pi);
	}

	public boolean isConstant() {
		switch (getNodeType()) {
			case LBRACK :
			case ASSIGN :
			case ADDITIVE_ASSIGNMENT_OP :
			case BITWISE_ASSIGNMENT_OP :
			case SHIFT_ASSIGNMENT_OP :
			case MULTIPLICATIVE_ASSIGNMENT_OP :
			case DOT :
				return false;
			case MULTIPLICATIVE_OP :
				if (getNodeText().equals("/"))
					return false;
			case ADDITIVE_OP :
			case EQUALITY_OP :
			case RELATIONAL_OP :
			case LOGICAL_OP :
			case IMPLICATION_OP :
			case BITWISE_OP :
			case SHIFT_OP :
				return left.isConstant() && right.isConstant();
			default :
				return false;
		}

	}

	public int getValue() {
		switch (getNodeType()) {
			case MULTIPLICATIVE_OP :
				if (getNodeText().equals("/"))
					throw new jml2b.exceptions.InternalError("getValue called for non constant expression");
			case ADDITIVE_OP :
				if (getNodeText().equals("+")) {
					return left.getValue() + right.getValue();
				} else if (getNodeText().equals("-")) {
					return left.getValue() - right.getValue();
				} else
					throw new jml2b.exceptions.InternalError("Unknown ADDITIVE_OP: " + getNodeText());
			case EQUALITY_OP :
				if (getNodeText().equals("==")) {
					return (left.getValue() == right.getValue()) ? 1 : 0;
				} else if (getNodeText().equals("!=")) {
					return (left.getValue() != right.getValue()) ? 1 : 0;
				} else
					throw new jml2b.exceptions.InternalError("Unknown EQUALITY_OP: " + getNodeText());
			case RELATIONAL_OP :
				if (getNodeText().equals(">=")) {
					return (left.getValue() >= right.getValue()) ? 1 : 0;
				} else if (getNodeText().equals("<=")) {
					return (left.getValue() <= right.getValue()) ? 1 : 0;
				} else if (getNodeText().equals("<")) {
					return (left.getValue() < right.getValue()) ? 1 : 0;
				} else if (getNodeText().equals(">")) {
					return (left.getValue() > right.getValue()) ? 1 : 0;
				} else
					throw new jml2b.exceptions.InternalError("Unknown RELATIONAL_OP: " + getNodeText());
			case LOGICAL_OP :
				if (getNodeText().equals("||")) {
					return ((left.getValue() != 0) || (right.getValue() != 0)) ? 1 : 0;
				} else if (getNodeText().equals("&&")) {
					return ((left.getValue() != 0) && (right.getValue() != 0)) ? 1 : 0;
				} else
					throw new jml2b.exceptions.InternalError("Unknown LOGICAL_OP: " + getNodeText());
			case IMPLICATION_OP :
				return (right.getValue() != 0) || (left.getValue() != 0) ? 1 : 0;
			case BITWISE_OP :
				if (getNodeText().equals("|")) {
					return left.getValue() | right.getValue();
				} else if (getNodeText().equals("&")) {
					return left.getValue() & right.getValue();
				} else if (getNodeText().equals("^")) {
					return left.getValue() ^ right.getValue();
				} else
					throw new jml2b.exceptions.InternalError("Unknown BITWISE_OP: " + getNodeText());
			case SHIFT_OP :
				if (getNodeText().equals(">>")) {
					return left.getValue() >> right.getValue();
				} else if (getNodeText().equals(">>>")) {
					return left.getValue() >>> right.getValue();
				} else if (getNodeText().equals("<<")) {
					return left.getValue() << right.getValue();
				} else
					throw new jml2b.exceptions.InternalError("Unknown SHIFT_OP: " + getNodeText());
			case LBRACK :
			case ASSIGN :
			case ADDITIVE_ASSIGNMENT_OP :
			case BITWISE_ASSIGNMENT_OP :
			case SHIFT_ASSIGNMENT_OP :
			case MULTIPLICATIVE_ASSIGNMENT_OP :
			case DOT :
			default :
				throw new jml2b.exceptions.InternalError("getValue called for non constant expression");
		}

	}

	//	Vector getFreshVars() {
	//		Vector res = left.getFreshVars();
	//		if (right != null)
	//			res.addAll(right.getFreshVars());
	//		return res;
	//	}

	public void old() {
		left.old();
		right.old();
	}

	/**
	 * Returns the left expression.
	 * 
	 * @return <code>left</code>
	 */
	public Expression getLeft() {
		return left;
	}

	/**
	 * Returns the right expression.
	 * 
	 * @return <code>right</code>
	 */
	public Expression getRight() {
		return right;
	}

	static final long serialVersionUID = 2767415478784994988L;

	
	public void collectCalledMethod(Vector calledMethod) {
		left.collectCalledMethod(calledMethod);
		right.collectCalledMethod(calledMethod);
	}

	void getFreeVariable(Set s) {
		left.getFreeVariable(s);
		right.getFreeVariable(s);
	}

}