//******************************************************************************
/* Copyright (c) 2002, 2003 GEMPLUS Software Research Labs. All Rights Reserved.
 /* Copyright (c) 2003, 2004 INRIA. All Rights Reserved.
 /*------------------------------------------------------------------------------
 /* Name: UnaryExp
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
import jml2b.formula.IFormToken;
import jml2b.formula.TerminalForm;
import jml2b.formula.UnaryForm;
import jml2b.link.LinkContext;
import jml2b.link.LinkInfo;
import jml2b.pog.lemma.FormulaWithPureMethodDecl;
import jml2b.structure.java.Field;
import jml2b.structure.java.JmlFile;
import jml2b.structure.java.Modifiers;
import jml2b.structure.java.ParsedItem;
import jml2b.structure.java.Type;
import jml2b.structure.jml.JmlExpression;
import antlr.collections.AST;

/**
 * This class implements unary expressions.
 * <p>
 * Java unary expressions can be:
 * <UL>
 * <li>!e
 * <li>-e
 * <li>e++
 * <li>e--
 * <li>++e
 * <li>--e
 * </UL>
 * Jml unary expressions can be:
 * <UL>
 * <li>\old(e)
 * <li>\fresh(e)
 * <li>\typeof(e)
 * <li>\elementtype(e)
 * </UL>
 * Proprietary expressions can be:
 * <UL>
 * <li>T_CALLED_OLD(e)
 * </UL>
 * 
 * @author L. Burdy, A. Requet
 */
public class UnaryExp extends Expression {

	/**
	 * The sub expression of the current expression.
	 */
	private Expression exp;

	/*
	 * @ @ invariant parsed ==> exp != null @ && parsed ==> exp.parsed; @
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
	UnaryExp(JmlFile jf, AST tree) {
		super(jf, tree);
	}

	/**
	 * Constructs an unary expression form another unary expression.
	 * 
	 * @param nodeType
	 *                    The node type
	 * @param nodeText
	 *                    The node text
	 * @param exp
	 *                    The sub expression
	 */
	/*
	 * @ @ requires exp != null; @
	 */
	public UnaryExp(int nodeType, String nodeText, Expression exp) {
		super(nodeType, nodeText);
		this.exp = exp;
		//@ set parsed = true;
	}

	public Object clone() {
		UnaryExp res = new UnaryExp(getNodeType(), getNodeText(), (Expression) exp.clone());
		res.setBox(this);
		res.setStateType(getStateType());
		return res;
	}

	public boolean equals(Expression e) {
		return getNodeType() == e.getNodeType() && exp.equals(((UnaryExp) e).exp);
	}

	/**
	 * Converts the expression in a formula with a context issue from the pure
	 * method call.
	 * <UL>
	 * <li><code>!e</code> is translated in <code>!e</code>
	 * <li><code>-e</code> is translated in <code>-e</code>
	 * <li><code>++e</code> is translated in <code>e + 1</code>
	 * <li><code>--e</code> is translated in <code>e - 1</code>
	 * <li><code>e++</code> is translated in <code>e</code>
	 * <li><code>e--</code> is translated in <code>e</code>
	 * <li><code>\old(e)</code> is translated in <code>\old(e)</code>
	 * <li><code>\fresh(e)</code> is translated in
	 * <code>!(e : \old(instances))</code>
	 * <li><code>\typeof(e)</code> is translated in <code>typeof(e)</code>
	 * <li><code>\elemtype(e)</code> is translated in
	 * <code>elemtype(e)</code>
	 * </UL>
	 */
	FormulaWithPureMethodDecl exprToContextForm(IJml2bConfiguration config, Vector methods, boolean pred)
			throws Jml2bException, PogException {
		byte n = -1;
		exp.exprToContextForm(config, methods, false);
		switch (getNodeType()) {
			case T_FRESH :
				return new FormulaWithPureMethodDecl(new UnaryForm(Ja_LNOT, new BinaryForm(B_IN, exp
						.exprToContextForm(config, methods, false).getFormula(), new UnaryForm(Jm_T_OLD,
						TerminalForm.instances))));
			case PRE_INCREMENT_OP :
				return new FormulaWithPureMethodDecl(new BinaryForm((getNodeText().equals("--")
						? Ja_ADD_OP
						: Ja_NEGATIVE_OP), exp.exprToContextForm(config, methods, false).getFormula(),
						new TerminalForm(1)));
			case POST_INCREMENT_OP :
				return new FormulaWithPureMethodDecl(exp.exprToContextForm(config, methods, false).getFormula());
			case LNOT : {
				FormulaWithPureMethodDecl l = exp.exprToContextForm(config, methods, true);
//				if (!pred) {
					UnaryForm res = new UnaryForm(Ja_LNOT, l.getFormula());
					res = new UnaryForm(B_BOOL, res);
					return new FormulaWithPureMethodDecl(l, res);
//				} else {
//					UnaryForm res = new UnaryForm(Ja_LNOT, l.getFormulaWithContext());
//					return new FormulaWithPureMethodDecl(res);
//				}
			}
			case UNARY_NUMERIC_OP :
				n = Ja_UNARY_NUMERIC_OP;
				break;
			case T_OLD :
				FormulaWithPureMethodDecl l = exp.exprToContextForm(config, methods, pred);
				l.old();
				
				UnaryForm res = new UnaryForm(Jm_T_OLD, l.getFormula());
				//			if (!pred)
				//				res = new UnaryForm(B_BOOL, res);
				return new FormulaWithPureMethodDecl(l,res);
			case MyToken.T_CALLED_OLD :
				n = IFormToken.T_CALLED_OLD;
				break;
			case MyToken.T_VARIANT_OLD :
				n = IFormToken.T_VARIANT_OLD;
				break;
			case T_ELEMTYPE :
				return new FormulaWithPureMethodDecl(new BinaryForm(IFormToken.B_APPLICATION, TerminalForm.elemtype, exp
						.exprToContextForm(config, methods, false).getFormula()));
			case T_TYPEOF :
				return new FormulaWithPureMethodDecl(new BinaryForm(IFormToken.B_APPLICATION, TerminalForm.typeof, exp
						.exprToContextForm(config, methods, false).getFormula()));
			default :
				throw new InternalError("UnaryExp.exprToForm " + getNodeType() + "\n" + "UnaryExp.exprToForm "
										+ nodeString[getNodeType()]);
		}
		UnaryForm res = new UnaryForm(n, exp.exprToContextForm(config, methods, false).getFormula());
		return new FormulaWithPureMethodDecl(res);
	}

	public String toJava(int indent) {
		switch (getNodeType()) {
			case T_TYPEOF :
				return "\\typeof(" + exp.toJava(indent) + ")";
			case T_ELEMTYPE :
				return "\\elemtype(" + exp.toJava(indent) + ")";
			case T_FRESH :
				return "\\fresh(" + exp.toJava(indent) + ")";
			case POST_INCREMENT_OP :
				return exp.toJava(indent) + getNodeText();
			case T_OLD :
				return "\\old(" + exp.toJava(indent) + ")";
			default :
				return getNodeText() + " " + exp.toJava(indent + getNodeText().length() + 1);
		}
	}

	public AST parse(AST tree) throws Jml2bException {
		//@ set parsed = true;
		setNodeType(tree.getType());
		setNodeText(tree.getText());
		exp = Expression.createE(getJmlFile(), tree.getFirstChild());
		exp.parse(tree.getFirstChild());
		return tree.getNextSibling();
	}

	public LinkInfo linkStatement(IJml2bConfiguration config, LinkContext f) throws Jml2bException {
		LinkInfo res = exp.linkStatement(config, f);

		switch (getNodeType()) {
			case PRE_INCREMENT_OP :
			case POST_INCREMENT_OP :
			case UNARY_NUMERIC_OP :
				setStateType(exp.getStateType());

				if (res.getType().getTag() == Type.T_INT) {
					return res;
				}
				return new LinkInfo(getStateType());

			case LNOT :
				setStateType(Type.getBoolean());

				if (res.getType().getTag() == Type.T_BOOLEAN) {
					return res;
				}
				return new LinkInfo(getStateType());

			case T_OLD :
			case T_FRESH :
				setStateType(exp.getStateType());
				return res;

			case T_TYPEOF :
				setStateType(new Type(Type.T_TYPE));
				return new LinkInfo(getStateType());
		}
		return null;
	}

	public Type typeCheck(IJml2bConfiguration config, LinkContext f) throws Jml2bException {
		Type t = exp.typeCheck(config, f);

		switch (getNodeType()) {
			case PRE_INCREMENT_OP :
			case POST_INCREMENT_OP :
				return t;
			case UNARY_NUMERIC_OP :
				if (t.isNumeric())
					return t.unaryPromote();
				throw new TypeCheckException("The operator " + getNodeText() + " is undefined for the argument type "
												+ t.toJava(), this);

			case LNOT :
				if (t.isBoolean())
					return Type.getBoolean();
				throw new TypeCheckException("The operator " + getNodeText() + " is undefined for the argument type "
												+ t.toJava(), this);

			case T_OLD :
			case T_FRESH :
				return t;

			case T_TYPEOF :
				if (t.isRef())
					return Type.getType();
				throw new TypeCheckException("The operator " + getNodeText() + " is undefined for the argument type "
												+ t.toJava(), this);
			case T_ELEMTYPE :
				if (t == Type.getType())
					return Type.getType();
				throw new TypeCheckException("The operator " + getNodeText() + " is undefined for the argument type "
												+ t.toJava(), this);
		}
		return null;
	}

	public void processIdent() {
		exp.processIdent();
	}

	public void isModifiersCompatible(IJml2bConfiguration config, Modifiers modifiers) throws LinkException {
		exp.isModifiersCompatible(config, modifiers);
	}

	public JmlExpression instancie() {
		exp = (Expression) exp.instancie();
		return this;
	}

	public Expression subField(Field f, Field newF) {
		exp = exp.subField(f, newF);
		return this;
	}

	public Expression subResult(String ww) {
		exp = exp.subResult(ww);
		return this;
	}

	public JmlExpression instancie(Expression b) {
		exp = (Expression) exp.instancie(b);
		return this;
	}

	public Vector getParsedItems() {
		Vector res = exp.getParsedItems();
		res.add((ParsedItem) this);
		return res;
	}

	public void setParsedItem(ParsedItem pi) {
		exp.setParsedItem(pi);
		change(pi);
	}

	public boolean isConstant() {
		switch (getNodeType()) {
			case POST_INCREMENT_OP :
			case PRE_INCREMENT_OP :
				return false;
			case UNARY_NUMERIC_OP :
			case LNOT :
				return exp.isConstant();
			default :
				return false;
		}
	}

	public int getValue() {
		switch (getNodeType()) {
			case LNOT :
				return (exp.getValue() != 0) ? 0 : 1;
			case UNARY_NUMERIC_OP :
				if (getNodeText().equals("-")) {
					return -exp.getValue();
				}
			default :
				throw new InternalError("Expression.getValue() called for " + "non-constant expression");
		}
	}

	//	Vector getFreshVars() {
	//		switch (getNodeType()) {
	//			case T_FRESH :
	//				Vector res = new Vector();
	//				res.add(exp);
	//				return res;
	//			default :
	//				return new Vector();
	//		}
	//	}

	public void old() {
		switch (getNodeType()) {
			case T_OLD :
				setNodeType(MyToken.T_CALLED_OLD);
				break;
			case T_FRESH :
				setNodeType(MyToken.T_FRESH_CALLED_OLD);
				break;
		}
	}

	public void collectCalledMethod(Vector calledMethod) {
		exp.collectCalledMethod(calledMethod);
	}

	static final long serialVersionUID = -7603371494507794174L;

	void getFreeVariable(Set s) {
		exp.getFreeVariable(s);
	}

	/**
	 * @return
	 */
	public Expression getExp() {
		return exp;
	}

}