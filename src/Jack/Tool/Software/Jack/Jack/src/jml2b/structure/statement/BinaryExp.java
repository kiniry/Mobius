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
import jml2b.pog.lemma.ExceptionalBehaviourStack;
import jml2b.pog.lemma.FormulaWithSpecMethodDecl;
import jml2b.pog.lemma.Proofs;
import jml2b.pog.lemma.SimpleLemma;
import jml2b.pog.lemma.VirtualFormula;
import jml2b.pog.substitution.SubArrayElementSingle;
import jml2b.pog.substitution.SubMemberField;
import jml2b.pog.substitution.SubStaticOrLocalField;
import jml2b.pog.substitution.SubTmpVar;
import jml2b.pog.util.ColoredInfo;
import jml2b.structure.java.Field;
import jml2b.structure.java.Identifier;
import jml2b.structure.java.JavaLoader;
import jml2b.structure.java.JmlFile;
import jml2b.structure.java.Modifiers;
import jml2b.structure.java.ParsedItem;
import jml2b.structure.java.Type;
import jml2b.structure.jml.JmlExpression;
import jml2b.util.ModifiableSet;
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
	FormulaWithSpecMethodDecl exprToContextForm(IJml2bConfiguration config, Vector methods, boolean pred)
			throws Jml2bException, PogException {
		FormulaWithSpecMethodDecl r, l;
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
								return new FormulaWithSpecMethodDecl(r, l, res);
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

					return new FormulaWithSpecMethodDecl(l, res);
				}
				
				else {
				res = new BinaryForm(IFormToken.ARRAY_ACCESS, new BinaryForm(IFormToken.B_APPLICATION, ElementsForm
						.getElementsName(left.getStateType().getElemType()), l.getFormula()), r.getFormula());
				if (pred)
					res = new BinaryForm(Ja_EQUALS_OP, res, new TerminalForm(Ja_LITERAL_true));

				return new FormulaWithSpecMethodDecl(r, l, res);
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
					return new FormulaWithSpecMethodDecl(r, l, res);
				}
			case SHIFT_OP :
				res = new BinaryForm(IFormToken.B_APPLICATION, new TerminalForm(getJFunction(getNodeText())),
						new BinaryForm(Ja_COMMA, l.getFormula(), r.getFormula()));
				return new FormulaWithSpecMethodDecl(r, l, res);
			case LOGICAL_OP :
					res = (getNodeText().equals("&&") ? 
							Formula.and(l.getFormula(), r.getFormula()) :
								Formula.or(l.getFormula(), r.getFormula()));
					if (!pred) 
					res = new UnaryForm(B_BOOL, res);
					return new FormulaWithSpecMethodDecl(l, r, res);
//				} else {
//					return new FormulaWithPureMethodDecl(new BinaryForm(
//							(getNodeText().equals("&&") ? Ja_AND_OP : Ja_OR_OP), l.getFormulaWithContext(), r
//									.getFormulaWithContext()));
//			}
			case IMPLICATION_OP :
					res = new BinaryForm(Jm_IMPLICATION_OP, l.getFormula(), r.getFormula());
					if (!pred) 
					res = new UnaryForm(B_BOOL, res);
					return new FormulaWithSpecMethodDecl(l, r, res);
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
						return new FormulaWithSpecMethodDecl(r, l, res);
					case EQUALITY_OP :
						if (getNodeText().equals("=="))
							n = Ja_EQUALS_OP;
						else
							n = Ja_DIFFERENT_OP;
						res = new BinaryForm(n, l.getFormula(), r.getFormula());
						if (!pred)
							res = new UnaryForm(B_BOOL, res);
						return new FormulaWithSpecMethodDecl(r, l, res);
					default :
						throw new InternalError("BinaryExp.exprToForm : bad node type  "
												+ MyToken.nodeString[getNodeType()] + " (" + getNodeType() + ")");
				}
				res = new BinaryForm(n, l.getFormula(), r.getFormula());
				return new FormulaWithSpecMethodDecl(r, l, res);
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
	 * Calculates the proofs resulting from the evaluation of an array access.
	 * 
	 * @param config
	 *                    the current configuration of the generator
	 * @param vv
	 *                    The temporary variable corresponding to the array object
	 * @param ww
	 *                    The temporary variable corresponding to the index
	 * @param normalBehaviour
	 *                    The current normal behaviour proof
	 * @param exceptionalBehaviour
	 *                    The current exceptional proofs stack
	 * @return The proofs resulting from the evaluation, that is:
	 *                <UL>
	 *                <li>the proof resulting from the throw of a NullPointerException
	 *                when the array object is null
	 *                <li>the proof resulting from the throw of an
	 *                ArrayIndexOutOfBoundsException when the index does not belong to
	 *                the bounds of the array
	 *                <li>the normal behaviour proof when all is right.
	 *                </UL>
	 */
	/*
	 * @ @ requires parsed; @
	 */
	Proofs lbrack(IJml2bConfiguration config, String leftVar, String vv, String ww, Proofs normalProof,
			ExceptionalBehaviourStack exceptionalProof) throws Jml2bException, PogException {

		// s = vv == null
		Formula s = new BinaryForm(Ja_EQUALS_OP, new TerminalForm(vv), new TerminalForm(Ja_LITERAL_null, "null"));

		// s1 is the condition corresponding to the fact that the index is in
		// the bounds of the array.
		// s1 = ww : 0 .. vv.length - 1
		Formula s1 = new BinaryForm(B_IN, new TerminalForm(ww), new BinaryForm(B_INTERVAL, new TerminalForm(0),
				new BinaryForm(Ja_NEGATIVE_OP, new BinaryForm(IFormToken.B_APPLICATION, TerminalForm
						.getArraylength(config), new TerminalForm(vv)), new TerminalForm(1))));

		// lv = normalBehaviour[leftVar <- xxxelements(vv)(ww)
		Proofs lv = normalProof.sub(new SubTmpVar(leftVar, new BinaryForm(IFormToken.ARRAY_ACCESS, new BinaryForm(
				IFormToken.B_APPLICATION, ElementsForm.getElementsName(left.getStateType().getElemType()),
				new TerminalForm(vv)), new TerminalForm(ww))));

		// adds the hypothesis that vv is not null
		lv.addHyp(Formula.not(s), new ColoredInfo(left), VirtualFormula.LOCALES);

		// adds the hypothesis that ww is in the array bounds
		lv.addHyp(s1, new ColoredInfo(right), VirtualFormula.LOCALES);

		// proof issued from the throw of an arrayIndexOutOfBoundsException
		Proofs lv1 = ((ExceptionalBehaviourStack) exceptionalProof.clone())
				.throwException(config, arrayIndexOutOfBoundsException);

		// adds the hypothesis that vv is not null
		lv1.addHyp(Formula.not(s), new ColoredInfo(left), VirtualFormula.LOCALES);

		// adds the hypothesis that ww is out of the array bounds
		lv1.addHyp(Formula.not(s1), new ColoredInfo(right, ColoredInfo.IS_OUT_OF_BOUNDS), VirtualFormula.LOCALES);

		lv.addAll(lv1);

		// evaluate the index with ww as resulting variable
		lv = right.wp(config, ww, lv, exceptionalProof);

		// proof issued from the throw of a nullPointerException
		lv1 = exceptionalProof.throwException(config, nullPointerException);

		// adds the hypothesis that vv is null
		lv1.addHyp(s, new ColoredInfo(left, ColoredInfo.IS_NULL), VirtualFormula.LOCALES);

		lv.addAll(lv1);

		// evaluate the array instance with vv as resulting variable
		return left.wp(config, vv, lv, exceptionalProof);
	}

	/**
	 * Calculates the proof resulting from the evaluation of an assignement.
	 * 
	 * @param config
	 *                    the current configuration of the generator
	 * @param resultingVar
	 *                    The temporary variable used to store the result of the
	 *                    evaluation of the assigned expression
	 * @param leftVar
	 *                    The temporary variable that represents the assigned variable
	 * @param normalBehaviour
	 *                    The current normal behaviour proof
	 * @param exceptionalBehaviour
	 *                    The current exceptional proofs stack
	 */
	/*
	 * @ @ requires parsed; @
	 */
	Proofs wpAssign(IJml2bConfiguration config, String result, String leftVar, Proofs normalProof,
			ExceptionalBehaviourStack exceptionalProof) throws Jml2bException, PogException {

		String vv = fresh();

		// An assignment can store its result in an instanciated member field,
		// a static field or an array at a certain index.
		switch (left.getNodeType()) {
			case DOT :
				// instance on whitch the assigned expression is assigned
				Expression instance = ((BinaryExp) left).left;
				// assigned expression
				Expression field = ((BinaryExp) left).right;
				if (field.getNodeType() == IDENT && ((TerminalExp) field).getIdent() != null
					&& ((TerminalExp) field).getIdent().idType == Identifier.ID_FIELD
					&& !((TerminalExp) field).getIdent().field.getModifiers().isStatic()) {
					// We assign into a member field.

					// vv represents the field.
					// xx represents the instance on which the field is applied.
					String xx = fresh();

					Proofs w = field
							.wp(config,
								vv,
								right.wp(	config,
											result,
											((Proofs) normalProof.clone()).addBox(new ColoredInfo(left))
													.sub(new SubMemberField(field.exprToForm(config).getFormula(), vv, xx,
															new TerminalForm(result))),
											exceptionalProof).sub(new SubTmpVar(leftVar, new BinaryForm(
										IFormToken.B_APPLICATION, new TerminalForm(vv), new TerminalForm(xx)))),
								exceptionalProof);

					// if the instance is not this, it can be null.
					if (instance.getNodeType() != LITERAL_this) {
						// t = xx == null
						Formula t = new BinaryForm(Ja_EQUALS_OP, new TerminalForm(xx), new TerminalForm(
								Ja_LITERAL_null, "null"));

						// u = xx != null
						Formula u = new UnaryForm(Ja_LNOT, t);

						// adds the hypothesis that the instance is not null
						w.addHyp(u, new ColoredInfo(instance), VirtualFormula.LOCALES);

						// Proof resulting from the throw of a
						// nullPointerException
						Proofs lv = exceptionalProof.throwException(config, nullPointerException);

						// adds the hypothesis that the instance is null
						lv.addHyp(t, new ColoredInfo(instance, ColoredInfo.IS_NULL), VirtualFormula.LOCALES);
						w.addAll(lv);
					}
					return instance.wp(config, xx, w, exceptionalProof);
				} else
					return field.wp(config, vv, right.wp(config, result, ((Proofs) normalProof.clone())
							.addBox(new ColoredInfo(this)).sub(new SubStaticOrLocalField(field.exprToForm(config).getFormula(),
									new TerminalForm(result))), exceptionalProof), exceptionalProof);
			case LBRACK :
				// ww is the temporary variable that represents the index.
				String ww = fresh();

				// type of the element of the array
				Type type = ((BinaryExp) left).left.getStateType().getElemType();

				// elements is the xxxelements function
				ElementsForm elements = ElementsForm.getElementsName(type);

				// t is the new xxxelements function
				// = elements <+ {vv |-> elements(vv) <+ {ww |-> resultingVar}}
				//				Formula t =
				//					new BinaryForm(
				//						B_OVERRIDING,
				//						elements,
				//						new BinaryForm(
				//							B_COUPLE,
				//							new TerminalForm(vv),
				//							new BinaryForm(
				//								B_OVERRIDING,
				//								new BinaryForm(
				//									IFormToken.B_APPLICATION,
				//									elements,
				//									new TerminalForm(vv)),
				//								new BinaryForm(
				//									B_COUPLE,
				//									new TerminalForm(ww),
				//									new TerminalForm(result)))));
				if (type.isBuiltin())
					// the array is an array of builtin type
					return ((BinaryExp) left).lbrack(	config,
														leftVar,
														vv,
														ww,
														right.wp(config, result, ((Proofs) normalProof.clone())
																.addBox(new ColoredInfo(left))
																.sub(new SubArrayElementSingle(elements,
																		new TerminalForm(vv), new TerminalForm(ww),
																		new TerminalForm(result))), exceptionalProof),
														exceptionalProof);
				else {
					// the array is an array of object. An arrayStoreException
					// can be thrown

					// u is the condition to not throw an arrayStoreException
					// u = resultingVar == null
					//     || typeof(resultingVar)
					//        : subtypes[{elemtype(typeof(vv))}]
					Formula u = new BinaryForm(Ja_OR_OP, new BinaryForm(Ja_EQUALS_OP, new TerminalForm(result),
							new TerminalForm(Ja_LITERAL_null, "null")), new BinaryForm(Jm_IS_SUBTYPE, new BinaryForm(
							IFormToken.B_APPLICATION, TerminalForm.$typeof, new TerminalForm(result)), new BinaryForm(
							IFormToken.B_APPLICATION, TerminalForm.$elemtype, new BinaryForm(IFormToken.B_APPLICATION,
									TerminalForm.$typeof, new TerminalForm(vv)))));

					Proofs lv = normalProof.addBox(new ColoredInfo(this)).sub(new SubArrayElementSingle(elements,
							new TerminalForm(vv), new TerminalForm(ww), new TerminalForm(result)));

					// adds the hypothesis that the type are compatible
					lv.addHyp(u, new ColoredInfo(right), VirtualFormula.LOCALES);

					// proof resulting from the throw of an arrayStoreException
					Proofs lv1 = exceptionalProof.throwException(config, arrayStoreException);

					// adds the hypothesis that the type are not compatible
					lv1.addHyp(	Formula.not(u),
								new ColoredInfo(this, ColoredInfo.IS_NOT_STORABLE),
								VirtualFormula.LOCALES);

					lv.addAll(lv1);

					return ((BinaryExp) left).lbrack(	config,
														leftVar,
														vv,
														ww,
														right.wp(config, result, lv, exceptionalProof),
														exceptionalProof);
				}
			case IDENT :
			case LITERAL_this :
				Proofs p = ((Proofs) normalProof.clone()).sub(new SubStaticOrLocalField(((TerminalExp) left)
						.exprToForm(config).getFormula(), new TerminalForm(result)));
				return right.wp(config, result, p.addBox(new ColoredInfo(left)), exceptionalProof).sub(new SubTmpVar(
						leftVar, left.exprToForm(config).getFormula()));
			default :
				throw new jml2b.exceptions.InternalError("binaryExp.wp : bad node type in ASSIGN " + left.getNodeType());
		}
	}

	/**
	 * Calculates the proof resulting from the evaluation of a dot.
	 * 
	 * @param config
	 *                    the current configuration of the generator
	 * @param resultingVar
	 *                    The temporary variable used to store the result of the
	 *                    evaluation
	 * @param normalBehaviour
	 *                    The current normal behaviour proof
	 * @param exceptionalBehaviour
	 *                    The current exceptional proofs stack
	 */
	/*
	 * @ @ requires parsed; @
	 */
	private Proofs wpDot(IJml2bConfiguration config, String result, Proofs normalProof,
			ExceptionalBehaviourStack exceptionalProof) throws Jml2bException, PogException {

		// The right expression should be an identifier.
		if (right.getNodeType() != IDENT)
			throw new jml2b.exceptions.InternalError("BinaryExp.wpDot : bad node type in DOT " + right.getNodeType());

		if (((TerminalExp) right).getIdent() == null)
			return right.wp(config,
							result,
							((Proofs) normalProof.clone()).addBox(new ColoredInfo(this)),
							exceptionalProof);

		switch (((TerminalExp) right).getIdent().idType) {
			case Identifier.ID_CLASS :
			case Identifier.ID_PACKAGE :
				return right.wp(config,
								result,
								((Proofs) normalProof.clone()).addBox(new ColoredInfo(this)),
								exceptionalProof);

			case Identifier.ID_FIELD :
				if (((TerminalExp) right).getIdent().field.getModifiers().isStatic())
					return right.wp(config, result, ((Proofs) normalProof.clone()).addBox(new ColoredInfo(this))
							.addBox(new ColoredInfo(left)), exceptionalProof);

				// vv represents the instance on witch the field is call.
				String vv = fresh();

				Formula s = new BinaryForm(IFormToken.B_APPLICATION, right.exprToForm(config).getFormula(), new TerminalForm(vv));

				// this cannot be null. This optimization allows to do not
				// generate the case where this == null.
				if (left.getNodeType() == LITERAL_this)
					return left.wp(config, vv, ((Proofs) normalProof.clone()).addBox(new ColoredInfo(this))
							.sub(new SubTmpVar(result, s)).addBox(new ColoredInfo(right)), exceptionalProof);

				Formula t = new BinaryForm(Ja_EQUALS_OP, new TerminalForm(vv),
						new TerminalForm(Ja_LITERAL_null, "null"));

				Formula u = new UnaryForm(Ja_LNOT, t);

				Proofs lv = ((Proofs) normalProof.clone()).addBox(new ColoredInfo(this)).sub(new SubTmpVar(result, s))
						.addBox(new ColoredInfo(right));
				lv.addHyp(u, new ColoredInfo(left), VirtualFormula.LOCALES);

				Proofs lv1 = exceptionalProof.throwException(config, nullPointerException);
				lv1.addHyp(	t,
							SimpleLemma.coloredInfos(left.getParsedItems(), ColoredInfo.IS_NULL),
							VirtualFormula.LOCALES);

				lv.addAll(lv1);
				return left.wp(config, vv, lv, exceptionalProof);
			default :
				throw new jml2b.exceptions.InternalError("BinaryExp.wp : bad node type in DOT Method met "
															+ right.getNodeType());
		}
	}

	/**
	 * Calculates the proof resulting from the evaluation of an assignement with
	 * operator.
	 * 
	 * @param config
	 *                    the current configuration of the generator
	 * @param resultingVar
	 *                    The temporary variable used to store the result of the
	 *                    evaluation
	 * @param normalBehaviour
	 *                    The current normal behaviour proof
	 * @param exceptionalBehaviour
	 *                    The current exceptional proofs stack
	 */
	/*
	 * @ @ requires parsed; @
	 */
	private Proofs wpAssignementOp(IJml2bConfiguration config, String result, Proofs normalProof,
			ExceptionalBehaviourStack exceptionalProof, String v1) throws Jml2bException, PogException {

		int type = 0;
		String text = getNodeText().substring(0, 1);

		switch (getNodeType()) {
			case ADDITIVE_ASSIGNMENT_OP :
				type = ADDITIVE_OP;
				break;
			case BITWISE_ASSIGNMENT_OP :
				type = BITWISE_OP;
				break;

			case SHIFT_ASSIGNMENT_OP :
				type = SHIFT_OP;
				text = getNodeText().substring(0, getNodeText().length() - 1);
				break;

			case MULTIPLICATIVE_ASSIGNMENT_OP :
				type = MULTIPLICATIVE_OP;
				break;
		}

		// e2 is left = v1 op right.
		BinaryExp e2 = new BinaryExp(ASSIGN, left, "=", new BinaryExp(type, new TerminalExp(v1, left.getStateType()),
				text, right));

		// The constructed assignment is evaluated, the formula resulting from
		// the evaluation of left will be strored into v1 in order to do not
		// evaluate two times left.
		return e2.wpAssign(	config,
							result,
							v1,
							((Proofs) normalProof.clone()).addBox(new ColoredInfo(this)),
							exceptionalProof);
	}

	public Proofs wp(IJml2bConfiguration config, String result, Proofs normalProof,
			ExceptionalBehaviourStack exceptionalProof) throws Jml2bException, PogException {

		Formula f1;
		Proofs p1, p2;

		// v1 is the result of the left expression evaluation.
		String v1 = fresh();
		// v2 is the result of the right expression evaluation.
		String v2 = fresh();

		switch (getNodeType()) {

			case DOT :
				return wpDot(config, result, normalProof, exceptionalProof);

			case ASSIGN :
				return wpAssign(config, result, fresh(), normalProof, exceptionalProof);

			case LBRACK :
				TerminalForm elements = ElementsForm.getElementsName(left.getStateType().getElemType());
				f1 = new BinaryForm(IFormToken.ARRAY_ACCESS, new BinaryForm(IFormToken.B_APPLICATION, elements,
						new TerminalForm(v1)), new TerminalForm(v2));
				return lbrack(	config,
								fresh(),
								v1,
								v2,
								((Proofs) normalProof.clone()).sub(new SubTmpVar(result, f1)),
								exceptionalProof);

			case ADDITIVE_ASSIGNMENT_OP :
			case BITWISE_ASSIGNMENT_OP :
			case SHIFT_ASSIGNMENT_OP :
			case MULTIPLICATIVE_ASSIGNMENT_OP :
				return wpAssignementOp(config, result, normalProof, exceptionalProof, v1);

			case LOGICAL_OP :
				// For and and or, right is evaluated only if left is not
				// respectively true and false.
				p1 = null;
				p2 = right.wp(config, result, normalProof, exceptionalProof);
				if (getNodeText().equals("&&")) {
					p2.addHyp(	new BinaryForm(Ja_EQUALS_OP, new TerminalForm(v1), new TerminalForm(Ja_LITERAL_true)),
								new ColoredInfo(left),
								VirtualFormula.LOCALES);
					p1 = ((Proofs) normalProof.clone()).sub(new SubTmpVar(result, new TerminalForm(Ja_LITERAL_false)));
					p1.addHyp(	new BinaryForm(Ja_EQUALS_OP, new TerminalForm(v1), new TerminalForm(Ja_LITERAL_false)),
								new ColoredInfo(left),
								VirtualFormula.LOCALES);
				} else {
					// or
					p2.addHyp(	new BinaryForm(Ja_EQUALS_OP, new TerminalForm(v1), new TerminalForm(Ja_LITERAL_false)),
								new ColoredInfo(left),
								VirtualFormula.LOCALES);
					p1 = ((Proofs) normalProof.clone()).sub(new SubTmpVar(result, new TerminalForm(Ja_LITERAL_true)));
					p1.addHyp(	new BinaryForm(Ja_EQUALS_OP, new TerminalForm(v1), new TerminalForm(Ja_LITERAL_true)),
								new ColoredInfo(left),
								VirtualFormula.LOCALES);
				}
				p2.addAll(p1);
				return left.wp(config, v1, p2, exceptionalProof);

			case MULTIPLICATIVE_OP :
				// The division and the modulo have a special treatment since
				// an exception is thrown when right is 0.
				if (getNodeText().equals("/") || getNodeText().equals("%")) {
					BinaryForm s = new BinaryForm(getNodeText().equals("/") ? Ja_DIV_OP : Ja_MOD, new TerminalForm(v1),
							new TerminalForm(v2));
					f1 = new BinaryForm(Ja_EQUALS_OP, new TerminalForm(v2), new TerminalForm(0));
					p1 = ((Proofs) normalProof.clone()).addBox(new ColoredInfo(this)).sub(new SubTmpVar(result, s));
					p1.addHyp(Formula.not(f1), new ColoredInfo(right), VirtualFormula.LOCALES);

					p2 = exceptionalProof.throwException(config, arithmeticException);
					p2.addHyp(f1, new ColoredInfo(right, ColoredInfo.EQUALS_0), VirtualFormula.LOCALES);

					p1.addAll(p2);

					return left.wp(config, v1, right.wp(config, v2, p1, exceptionalProof), exceptionalProof);
				}
			// else continue with the ADDITIVE_OP

			case ADDITIVE_OP :
				f1 = new BinaryForm(getNodeText().equals("+") ? Ja_ADD_OP : (getNodeText().equals("*")
						? Ja_MUL_OP
						: Ja_NEGATIVE_OP), new TerminalForm(v1), new TerminalForm(v2));
				break;

			case EQUALITY_OP :
			case RELATIONAL_OP :
				f1 = new UnaryForm(B_BOOL, new BinaryForm(getNodeType() == EQUALITY_OP ? (getNodeText().equals("==")
						? Ja_EQUALS_OP
						: Ja_DIFFERENT_OP) : (getNodeText().equals("<=") ? Ja_LE_OP : (getNodeText().equals("<")
						? Ja_LESS_OP
						: (getNodeText().equals(">=") ? Ja_GE_OP : Ja_GREATER_OP))), new TerminalForm(v1),
						new TerminalForm(v2)));
				break;

			case IMPLICATION_OP :

				// f1 = bool(v1 == TRUE ==> v2 == TRUE)
				f1 = new UnaryForm(B_BOOL, new BinaryForm(Jm_IMPLICATION_OP, new BinaryForm(Ja_EQUALS_OP,
						new TerminalForm(v1), new TerminalForm(Ja_LITERAL_true)), new BinaryForm(Ja_EQUALS_OP,
						new TerminalForm(v2), new TerminalForm(Ja_LITERAL_true))));

				break;

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
					f1 = new BinaryForm(token, new TerminalForm(v1), new TerminalForm(v2));

				}
			case SHIFT_OP :

				// f1 = j_xxx(vv1, vv2)
				f1 = new BinaryForm(IFormToken.B_APPLICATION, new TerminalForm(getJFunction(getNodeText())),
						new BinaryForm(Ja_COMMA, new TerminalForm(v1), new TerminalForm(v2)));
				break;
			case COMMA :
				// comma treated here are those which appears in for initializer
				// and
				// updater.
				f1 = new TerminalForm(v1);
				break;
			default :
				throw new jml2b.exceptions.InternalError("BinaryExp.wp : bad node type " + getNodeType());
		}

		// Evaluates left and right with result substituted with f1.
		return left.wp(config, v1, right.wp(config, v2, ((Proofs) normalProof.clone()).addBox(new ColoredInfo(this))
				.sub(new SubTmpVar(result, f1)), exceptionalProof), exceptionalProof);
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

	public void getPrecondition(IJml2bConfiguration config, ModifiableSet modifies, Vector req, Vector ens)
			throws Jml2bException, PogException {
		left.getPrecondition(config, modifies, req, ens);
		right.getPrecondition(config, modifies, req, ens);
	}

	public void collectCalledMethod(Vector calledMethod) {
		left.collectCalledMethod(calledMethod);
		right.collectCalledMethod(calledMethod);
	}

	void getFreeVariable(Set s) {
		left.getFreeVariable(s);
		right.getFreeVariable(s);
	}

}