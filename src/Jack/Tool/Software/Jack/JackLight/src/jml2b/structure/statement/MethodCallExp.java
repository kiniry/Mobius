//******************************************************************************
/* Copyright (c) 2002, 2003 GEMPLUS Software Research Labs. All Rights Reserved.
 /* Copyright (c) 2003, 2004 INRIA. All Rights Reserved.
 /*------------------------------------------------------------------------------
 /* Name: MethodCallExp
 /*
 /*******************************************************************************
 /* Warnings/Remarks:
 /*  09/26/2003 : Simplify integration achieved
 /******************************************************************************/
package jml2b.structure.statement;

import jack.util.Logger;

import java.util.Set;
import java.util.Vector;

import jml2b.IJml2bConfiguration;
import jml2b.exceptions.Jml2bException;
import jml2b.exceptions.LinkException;
import jml2b.exceptions.PogException;
import jml2b.formula.BinaryForm;
import jml2b.formula.DeclPureMethodForm;
import jml2b.formula.ElementsForm;
import jml2b.formula.Formula;
import jml2b.formula.IFormToken;
import jml2b.formula.MethodCallForm;
import jml2b.formula.QuantifiedVarForm;
import jml2b.formula.TTypeForm;
import jml2b.formula.TerminalForm;
import jml2b.link.LinkContext;
import jml2b.link.LinkInfo;
import jml2b.pog.lemma.FormulaWithPureMethodDecl;
import jml2b.structure.AMethod;
import jml2b.structure.IAParameters;
import jml2b.structure.java.CoqDefinedMethod;
import jml2b.structure.java.Field;
import jml2b.structure.java.Identifier;
import jml2b.structure.java.JmlFile;
import jml2b.structure.java.Method;
import jml2b.structure.java.Modifiers;
import jml2b.structure.java.Parameters;
import jml2b.structure.java.ParsedItem;
import jml2b.structure.java.Type;
import jml2b.structure.jml.JmlExpression;
import antlr.collections.AST;

/**
 * This class implements a method call expression
 * 
 * @author L. Burdy, A. Requet
 */
public class MethodCallExp extends Expression {

	/**
	 * Returns a set of fresh variables, each one corresponding to a parameter
	 * of the method.
	 * 
	 * @param signature
	 *            The signature of the method
	 * @return a set of fresh variables.
	 */
	public static Vector renamedParam(IAParameters signature) {
		Vector res = new Vector();
		for (int i = 0; i < signature.nparams(); i++)
			res.add(fresh());
		return res;
	}

	/**
	 * The expression corresponding to the called method
	 */
	private Expression left;

	/*
	 * @ @ invariant parsed ==> left != null; @
	 */

	/**
	 * The arguments expression, it can be possibly <code>null</code> when the
	 * method is called without arguments.
	 */
	private Expression right;

	/**
	 * Constructs an expression as a <i>parsed item</i>.
	 * 
	 * @param jf
	 *            The file where the statement is located
	 * @param tree
	 *            The <code>AST</code> node corresponding to the statement
	 * @see jml2b.structure.java.ParsedItem#ParsedItem(JmlFile, AST)
	 */
	protected MethodCallExp(JmlFile jf, AST tree) {
		super(jf, tree);
	}

	/**
	 * Constructs a method call expression form another one
	 * 
	 * @param nodeType
	 *            The node type
	 * @param nodeText
	 *            The node text
	 * @param left
	 *            The left expression
	 * @param right
	 *            The right expression
	 */
	/*
	 * @ @ requires left != null; @
	 */
	public MethodCallExp(int nodeType, Expression left, String nodeText, Expression right) {
		super(nodeType, nodeText);
		this.left = left;
		this.right = right;
		// @ set parsed = true;
	}

	public Object clone() {
		MethodCallExp res = new MethodCallExp(getNodeType(), (Expression) left.clone(), getNodeText(), right == null
				? null
				: (Expression) right.clone());
		res.setBox(this);
		res.setStateType(getStateType());
		return res;
	}

	public boolean equals(Expression e) {
		return getNodeType() == e.getNodeType()
				&& left.equals(((MethodCallExp) e).left)
				&& (right == null ? ((MethodCallExp) e).right == null : (((MethodCallExp) e).right != null && right
						.equals(((MethodCallExp) e).right)));
	}

	/**
	 * A method call corresponding to a pure method is translated. If the
	 * ensures clause corresponds to an expression that match whith
	 * <code>\result == e</code> then the method call is translated into
	 * <code>e</code> where the parameters have been substitute. If the
	 * ensures clause is a general expression <code>e</code>, then the method
	 * call is converted in <code>\forall type result; e</code> where the
	 * parameters have been substituted. This convertion is not direct, since
	 * the predicate cannot be integrated into all engloging expression, so the
	 * result of the convertion is stored into a {@link ContextFromPureMethod}
	 * structure.
	 */
	FormulaWithPureMethodDecl exprToContextForm(IJml2bConfiguration config, Vector methods, boolean pred)
			throws Jml2bException, PogException {

		// m is the called method
		AMethod m;

		// f is the ensures clause of the called method
		Expression f;

		Expression instance = null;

		switch (left.getNodeType()) {
			case DOT :
				m = ((TerminalExp) ((BinaryExp) left).getRight()).getIdent().mth;

				f = (Expression) m.getNormalizedEnsures(config).clone();
				f.old();
				instance = ((BinaryExp) left).getLeft();
				// f = (Expression) f.instancie();
				break;
			case IDENT :
			case LITERAL_super :
			case LITERAL_this :
				m = ((TerminalExp) left).getIdent().mth;
				f = (Expression) m.getNormalizedEnsures(config).clone();
				f.old();
				break;
			default :
				throw new jml2b.exceptions.InternalError("exprToForm : bad node type in METHOD_CALL "
															+ left.getNodeType());
		}

		// ww represents the result of the operation call.
		String ww = freshResult(m.getName());
		String wwr = "Result_";
		String mm = freshMethod(m.getName());

		// If the method called already belongs to the set of already
		// met methods, then an exception is thrown.
		// FIXME: it is no more accurate.
//		if (methods.indexOf(m) != -1) {
//			String error = "A method called loop was founded in specifications :";
//			boolean first = true;
//			for (int i = methods.indexOf(m); i < methods.size(); i++) {
//				Method element = (Method) methods.elementAt(i);
//				if (first) {
//					first = false;
//					error += " " + element.getName();
//				} else
//					error += " -> " + element.getName();
//			}
//			error += " -> " + m.getName();
//			throw new PogException(error, this);
//		}

		// The method parameters are converted.
		// param is the set of converted parameter formula
		// p is the result of the convertion, it possibly corresponds to a
		// context
		Vector param = null;
		FormulaWithPureMethodDecl p = null;
		if (right != null) {
			p = right.exprToContextForm(config, methods, false);
			param = p.getFormula().toVector();
		}

		// Adds the method to the already met method set.
		methods.add(m);

		FormulaWithPureMethodDecl c;

		if (f.getNodeType() == EQUALITY_OP && f.getNodeText().equals("==")
			&& ((BinaryExp) f).getLeft().getNodeType() == T_RESULT) {
			//The ensures of the method match with \result == a.
			return exprToContext_simpleResult(instance, f, param, config,  methods, pred, p, m);
		} else {
			f = f.subResult(wwr);
			QuantifiedVarForm w = null;
			Object par = m.getParams();
			Vector e1 = null;
			if(par instanceof Parameters)
				e1 = ((Parameters) par).getSignature();
			else {
				e1 = new Vector();
				IAParameters cp = (IAParameters) par;
				Logger.get().println(cp.nparams());
				Logger.get().println(par.getClass());
//				Logger.get().println();
			}

			Formula coqMethodParam = null;
			boolean inte = false, refe = false, shorte = false, bytee = false, chare = false, boole = false;

			// adding this
			if(!m.isStatic()) {
				if(coqMethodParam == null) {
					coqMethodParam = new TerminalForm(IFormToken.Ja_LITERAL_this, "this");
				}
				else 
					coqMethodParam = new BinaryForm(IFormToken.Ja_COMMA, new TerminalForm(IFormToken.Ja_LITERAL_this, "this"), coqMethodParam);
			}
			// Adding fields
			for (int i=e1.size()-1; i >= 0; i--) {
				Field fi = (Field) e1.get(i);
				w = new QuantifiedVarForm(new TerminalForm(new Identifier(fi)), new TTypeForm(IFormToken.T_TYPE, fi
						.getType()), w);
				
				if (coqMethodParam == null)
					coqMethodParam = new TerminalForm(new Identifier(fi));
				else
					coqMethodParam = new BinaryForm(IFormToken.Ja_COMMA, new TerminalForm(new Identifier(fi)), coqMethodParam);
				
				if (fi.getType().isArray()) {
					inte = inte || fi.getType().getElemType().equals(Type.getInteger());
					refe = refe || fi.getType().getElemType().isRef();
					shorte= shorte || fi.getType().getElemType().equals(Type.getShort());
					bytee = bytee || fi.getType().getElemType().equals(Type.getByte());
					chare = chare || fi.getType().getElemType().equals(Type.getChar());
					boole  = boole || fi.getType().getElemType().isBoolean();
				}
			}
			
			
			//FIXME: the accessors should be added here and not below
		

			
			
			if (param == null) {
				FormulaWithPureMethodDecl fwp;
				if ((m instanceof Method) && ((Method) m).isCoqDef()) {
					if (!m.isStatic()) {
						fwp = new FormulaWithPureMethodDecl(new BinaryForm(IFormToken.Ja_EQUALS_OP, 
								new TerminalForm(wwr), 
								new BinaryForm(IFormToken.B_APPLICATION,
			                             new TerminalForm(new Identifier(new CoqDefinedMethod((Method) m))),
			                             coqMethodParam)));
					}
					else {
						fwp = new FormulaWithPureMethodDecl(new BinaryForm(IFormToken.Ja_EQUALS_OP, 
								new TerminalForm(wwr), 
		                             new TerminalForm(new Identifier(new CoqDefinedMethod((Method) m)))));

					}
				} 
				else {
					fwp = f.predToForm(config); 
				}
				
				if(instance != null) {
					FormulaWithPureMethodDecl instanceWpmd = 
						instance.exprToForm(config, methods, false);
					Formula mcf = new MethodCallForm(mm, null, instance != null
							? instanceWpmd.getFormula()
									: null, ww, new TTypeForm(IFormToken.T_TYPE, m.getReturnType()));
					if (pred) {
						mcf = new BinaryForm(Ja_EQUALS_OP, mcf, new TerminalForm(Ja_LITERAL_true));
					}
					c = new FormulaWithPureMethodDecl(instanceWpmd, fwp, mcf, new DeclPureMethodForm(new TerminalForm(mm), 
							m.isStatic() ? null
									: new TTypeForm(IFormToken.T_TYPE, new Type(m.getDefiningClass())), 
									null, wwr, 
									new TTypeForm(IFormToken.T_TYPE, m.getReturnType()), fwp.getFormula()));
				}
				else {
					Formula mcf = new MethodCallForm(mm, null, null, 
							ww, new TTypeForm(IFormToken.T_TYPE, m.getReturnType()));
					if (pred) {
						mcf = new BinaryForm(Ja_EQUALS_OP, mcf, new TerminalForm(Ja_LITERAL_true));
					}
					c = new FormulaWithPureMethodDecl(fwp, mcf, new DeclPureMethodForm(new TerminalForm(mm), 
							m.isStatic() ? null
									: new TTypeForm(IFormToken.T_TYPE, new Type(m.getDefiningClass())), 
									null, wwr, 
									new TTypeForm(IFormToken.T_TYPE, m.getReturnType()), fwp.getFormula()));

				}

			} else {
				Formula pf = p.getFormula();
				if (inte) {
					w = new QuantifiedVarForm(ElementsForm.intelements, ElementsForm.intelements.getType(), w);
					pf = new BinaryForm(IFormToken.Ja_COMMA, ElementsForm.intelements, pf);
					coqMethodParam = new BinaryForm(IFormToken.Ja_COMMA, ElementsForm.intelements, coqMethodParam);
				}
				if (refe) {
					w = new QuantifiedVarForm(ElementsForm.refelements, ElementsForm.refelements.getType(), w);
					pf = new BinaryForm(IFormToken.Ja_COMMA, ElementsForm.refelements, pf);
					coqMethodParam = new BinaryForm(IFormToken.Ja_COMMA, ElementsForm.refelements, coqMethodParam);
				}
				if (shorte) {
					w = new QuantifiedVarForm(ElementsForm.shortelements, ElementsForm.shortelements.getType(), w);
					pf = new BinaryForm(IFormToken.Ja_COMMA, ElementsForm.shortelements, pf);
					coqMethodParam = new BinaryForm(IFormToken.Ja_COMMA, ElementsForm.shortelements, coqMethodParam);
				}
				if (bytee) {
					w = new QuantifiedVarForm(ElementsForm.byteelements, ElementsForm.byteelements.getType(), w);
					pf = new BinaryForm(IFormToken.Ja_COMMA, ElementsForm.byteelements, pf);
					coqMethodParam = new BinaryForm(IFormToken.Ja_COMMA, ElementsForm.byteelements, coqMethodParam);
				}
				if (chare) {
					w = new QuantifiedVarForm(ElementsForm.charelements, ElementsForm.charelements.getType(), w);
					pf = new BinaryForm(IFormToken.Ja_COMMA, ElementsForm.charelements, pf);
					coqMethodParam = new BinaryForm(IFormToken.Ja_COMMA, ElementsForm.charelements, coqMethodParam);
				}
				if (boole) {
					w = new QuantifiedVarForm(ElementsForm.booleanelements, ElementsForm.booleanelements.getType(), w);
					pf = new BinaryForm(IFormToken.Ja_COMMA, ElementsForm.booleanelements, pf);
					coqMethodParam = new BinaryForm(IFormToken.Ja_COMMA, ElementsForm.booleanelements, coqMethodParam);
				}
//				if (!m.isStatic())
//					coqMethodParam = new BinaryForm(IFormToken.Ja_COMMA, new TerminalForm(IFormToken.Ja_LITERAL_this, "this"), coqMethodParam);
				FormulaWithPureMethodDecl f1 = f.exprToForm(config, methods, true).renameParam(m.getParams(), param);
				Formula fwp;
				if ((m instanceof Method ) && ((Method) m).isCoqDef())
					fwp = new BinaryForm(IFormToken.Ja_EQUALS_OP, new TerminalForm(wwr), 
					                     new BinaryForm(IFormToken.B_APPLICATION,
							                             new TerminalForm(new Identifier(new CoqDefinedMethod((Method) m))),
							                             coqMethodParam));
				else
					fwp = f.exprToForm(config, methods, true).getFormula();
				
				FormulaWithPureMethodDecl instanceWpmd = instance != null ? instance.exprToForm(config, methods, false)
						 : null;
				Formula mcf = new MethodCallForm(mm, pf, instanceWpmd != null ? instanceWpmd.getFormula() : null, ww, new TTypeForm(IFormToken.T_TYPE, m.getReturnType()));
				if (pred)
					mcf = new BinaryForm(Ja_EQUALS_OP, mcf, new TerminalForm(Ja_LITERAL_true));
				if (instanceWpmd != null)
				c = new FormulaWithPureMethodDecl(instanceWpmd,p,f1, mcf, new DeclPureMethodForm(new TerminalForm(mm), m.isStatic()
						? null
						: new TTypeForm(IFormToken.T_TYPE, new Type(m.getDefiningClass())), w, wwr, new TTypeForm(
						IFormToken.T_TYPE, m.getReturnType()), fwp));
				else
					c = new FormulaWithPureMethodDecl(p,f1, mcf, new DeclPureMethodForm(new TerminalForm(mm), m.isStatic()
					                                                         						? null
					                                                         						: new TTypeForm(IFormToken.T_TYPE, new Type(m.getDefiningClass())), w, wwr, new TTypeForm(
					                                                         						IFormToken.T_TYPE, m.getReturnType()), fwp));

			}
		}

		// Removes the method from the already met method set.
		methods.remove(m);

		return c;
	}

	private FormulaWithPureMethodDecl exprToContext_simpleResult(Expression instance, Expression f, Vector param,  
			IJml2bConfiguration config, Vector methods, boolean pred,
			FormulaWithPureMethodDecl p, AMethod m) throws PogException, Jml2bException {
		FormulaWithPureMethodDecl c;
		if (instance != null)
			f.instancie(instance);
		//The ensures of the method match with \result == a.
		if (param == null){	
			c = ((BinaryExp) f).getRight().exprToForm(config, methods, pred);
		}
		else {
			FormulaWithPureMethodDecl fwp = ((BinaryExp) f).getRight().exprToForm(config, methods, pred)
					.renameParam((Parameters) m.getParams(), param);
			c = new FormulaWithPureMethodDecl(fwp, p, fwp.getFormula());
		}
		return c;
	}
	
	
	public String toJava(int indent) {
		return left.toJava(indent) + "(" + (right == null ? "" : right.toJava(indent)) + ")";
	}

	public AST parse(AST tree) throws Jml2bException {
		// @ set parsed = true;
		AST subtree;
		setNodeType(tree.getType());
		setNodeText(tree.getText());
		setNodeType(IFormToken.METHOD_CALL);
		left = Expression.createE(getJmlFile(), tree.getFirstChild());
		subtree = left.parse(tree.getFirstChild());
		if (subtree != null) {
			right = Expression.createE(getJmlFile(), tree.getFirstChild().getNextSibling());
			right.parse(tree.getFirstChild().getNextSibling());
		}
		return tree.getNextSibling();
	}

	public LinkInfo linkStatement(IJml2bConfiguration config, LinkContext f) throws Jml2bException {
		LinkInfo result;

		// create a new vector for holding the parameters
		Vector parameters = new Vector();

		// if no parameters to method, right == null.
		if (right != null) {
			right.linkParameters(config, f, parameters);
		}
		// left = a gauche de la parenthese
		result = left.linkMethod(config, f, parameters);

		// le type d'un noeud method_call correspond au type de
		// retour de la m?thode appell?e
		if (result != null) {
			setStateType(result.getType());
		} else {
			setStateType(null);
		}

		return result;
	}

	public Type typeCheck(IJml2bConfiguration config, LinkContext f) throws Jml2bException {
		if (right != null) {
			right.typeCheck(config, f);
		}
		left.typeCheck(config, f);
		return getStateType();
	}

	public void processIdent() {
		left.processIdent();
		if (right != null)
			right.processIdent();
	}

	public void isModifiersCompatible(IJml2bConfiguration config, Modifiers modifiers) throws LinkException {
		left.isModifiersCompatible(config, modifiers);
		if (right != null)
			right.isModifiersCompatible(config, modifiers);
	}

	public JmlExpression instancie() {
		left = (Expression) left.instancie();
		if (right != null)
			right = (Expression) right.instancie();
		return this;
	}

	public Expression subField(Field f, Field newF) {
		right = (right == null ? null : right.subField(f, newF));
		return this;
	}

	public Expression subResult(String ww) {
		left = (Expression) left.subResult(ww);
		right = (right == null ? null : right.subResult(ww));
		return this;
	}

	public JmlExpression instancie(Expression b) {
		left = (Expression) left.instancie(b);
		right = (right == null ? null : (Expression) right.instancie(b));
		return this;
	}

	public Vector getParsedItems() {
		Vector res = left.getParsedItems();
		if (right != null)
			res.addAll(right.getParsedItems());
		res.add((ParsedItem) this);
		return res;
	}

	public void setParsedItem(ParsedItem pi) {
		left.setParsedItem(pi);
		if (right != null)
			right.setParsedItem(pi);
		change(pi);
	}

	public boolean isConstant() {
		return false;
	}

	public int getValue() {
		throw new jml2b.exceptions.InternalError("getValue called for non constant expression");
	}

	// Vector getFreshVars() {
	// Vector res = left.getFreshVars();
	// if (right != null)
	// res.addAll(right.getFreshVars());
	// return res;
	// }

	public void old() {
		left.old();
		if (right != null)
			right.old();
	}

	/**
	 * Returns the expression corresponding to the called method.
	 * 
	 * @return <code>left</code>
	 */
	public Expression getLeft() {
		return left;
	}

	static final long serialVersionUID = 7743883423438724253L;

	public void collectCalledMethod(Vector calledMethod) {
		switch (left.getNodeType()) {
			case DOT :
				calledMethod.add(((TerminalExp) ((BinaryExp) left).getRight()).getIdent().mth);
				break;
			case IDENT :
			case LITERAL_super :
			case LITERAL_this :
				calledMethod.add(((TerminalExp) left).getIdent().mth);
				break;
			default :
				throw new jml2b.exceptions.InternalError("BinaryExp.getPrecondition : bad node type in METHOD_CALL "
															+ left.getNodeType());
		}
	}

	void getFreeVariable(Set s) {
	}
	/**
	 * @return
	 */
	public Expression getRight() {
		return right;
	}
}


//
// //******************************************************************************
// /* Copyright (c) 2002, 2003 GEMPLUS Software Research Labs. All Rights
// Reserved.
// /* Copyright (c) 2003, 2004 INRIA. All Rights Reserved.
// /*------------------------------------------------------------------------------
// /* Name: MethodCallExp
// /*
// /*******************************************************************************
// /* Warnings/Remarks:
// /* 09/26/2003 : Simplify integration achieved
// /******************************************************************************/
// package jml2b.structure.statement;
//
// import java.util.Enumeration;
// import java.util.HashSet;
// import java.util.Set;
// import java.util.Vector;
//
// import jml2b.IJml2bConfiguration;
// import jml2b.exceptions.Jml2bException;
// import jml2b.exceptions.LinkException;
// import jml2b.exceptions.PogException;
// import jml2b.formula.BinaryForm;
// import jml2b.formula.Formula;
// import jml2b.formula.IFormToken;
// import jml2b.formula.MethodCallForm;
// import jml2b.formula.TerminalForm;
// import jml2b.formula.UnaryForm;
// import jml2b.link.LinkContext;
// import jml2b.link.LinkInfo;
// import jml2b.pog.lemma.ExceptionalBehaviourStack;
// import jml2b.pog.lemma.GoalOrigin;
// import jml2b.pog.lemma.Proofs;
// import jml2b.pog.lemma.SimpleLemma;
// import jml2b.pog.lemma.Theorem;
// import jml2b.pog.lemma.VirtualFormula;
// import jml2b.pog.substitution.SubTmpVar;
// import jml2b.pog.util.ColoredInfo;
// import jml2b.pog.util.ContextFromPureMethod;
// import jml2b.structure.AMethod;
// import jml2b.structure.IAParameters;
// import jml2b.structure.java.Field;
// import jml2b.structure.java.JmlFile;
// import jml2b.structure.java.Method;
// import jml2b.structure.java.Modifiers;
// import jml2b.structure.java.Parameters;
// import jml2b.structure.java.ParsedItem;
// import jml2b.structure.java.Type;
// import jml2b.structure.jml.JmlExpression;
// import jml2b.structure.jml.ModifiesClause;
// import jml2b.structure.jml.SpecCase;
// import jml2b.util.ModifiableSet;
// import antlr.collections.AST;
//
// /**
// * This class implements a method call expression
// *
// * @author L. Burdy, A. Requet
// */
// public class MethodCallExp extends Expression {
//
// /**
// * Returns a set of fresh variables, each one corresponding to a parameter
// * of the method.
// *
// * @param signature
// * The signature of the method
// * @return a set of fresh variables.
// */
// public static Vector renamedParam(IAParameters signature) {
// Vector res = new Vector();
// for (int i = 0; i < signature.nparams(); i++)
// res.add(fresh());
// return res;
// }
//
// /**
// * The expression corresponding to the called method
// */
// private Expression left;
//
// /*
// * @ @ invariant parsed ==> left != null; @
// */
//
// /**
// * The arguments expression, it can be possibly <code>null</code> when the
// * method is called without arguments.
// */
// private Expression right;
//
// /**
// * Constructs an expression as a <i>parsed item</i>.
// *
// * @param jf
// * The file where the statement is located
// * @param tree
// * The <code>AST</code> node corresponding to the statement
// * @see jml2b.structure.java.ParsedItem#ParsedItem(JmlFile, AST)
// */
// protected MethodCallExp(JmlFile jf, AST tree) {
// super(jf, tree);
// }
//
// /**
// * Constructs a method call expression form another one
// *
// * @param nodeType
// * The node type
// * @param nodeText
// * The node text
// * @param left
// * The left expression
// * @param right
// * The right expression
// */
// /*
// * @ @ requires left != null; @
// */
// public MethodCallExp(int nodeType, Expression left, String nodeText,
// Expression right) {
// super(nodeType, nodeText);
// this.left = left;
// this.right = right;
// // @ set parsed = true;
// }
//
// public Object clone() {
// MethodCallExp res = new MethodCallExp(getNodeType(), (Expression)
// left.clone(), getNodeText(), right == null
// ? null
// : (Expression) right.clone());
// res.setBox(this);
// res.setStateType(getStateType());
// return res;
// }
//
// public boolean equals(Expression e) {
// return getNodeType() == e.getNodeType()
// && left.equals(((MethodCallExp) e).left)
// && (right == null ? ((MethodCallExp) e).right == null : (((MethodCallExp)
// e).right != null && right
// .equals(((MethodCallExp) e).right)));
// }
//
// /**
// * A method call corresponding to a pure method is translated. If the
// * ensures clause corresponds to an expression that match whith
// * <code>\result == e</code> then the method call is translated into
// * <code>e</code> where the parameters have been substitute. If the
// * ensures clause is a general expression <code>e</code>, then the method
// * call is converted in <code>\forall type result; e</code> where the
// * parameters have been substituted. This convertion is not direct, since
// * the predicate cannot be integrated into all engloging expression, so the
// * result of the convertion is stored into a {@link ContextFromPureMethod}
// * structure.
// */
// ContextFromPureMethod exprToContextForm(IJml2bConfiguration config, Vector
// methods, boolean pred)
// throws Jml2bException, PogException {
//
// // m is the called method
// AMethod m;
//
// // f is the ensures clause of the called method
// Expression f;
//
// Expression instance = null;
//
// switch (left.getNodeType()) {
// case DOT :
// m = ((TerminalExp) ((BinaryExp) left).getRight()).getIdent().mth;
//
// f = (Expression) m.getNormalizedEnsures(config).clone();
// f.old();
// instance = ((BinaryExp) left).getLeft();
// // f = (Expression) f.instancie();
// break;
// case IDENT :
// case LITERAL_super :
// case LITERAL_this :
// m = ((TerminalExp) left).getIdent().mth;
// f = (Expression) m.getNormalizedEnsures(config).clone();
// f.old();
// break;
// default :
// throw new jml2b.exceptions.InternalError("exprToForm : bad node type in
// METHOD_CALL "
// + left.getNodeType());
// }
//
// // ww represents the result of the operation call.
// String ww = freshResult(m.getName());
//
// // If the method called already belongs to the set of already
// // met methods, then an exception is thrown.
// if (methods.indexOf(m) != -1) {
// String error = "A method called loop was founded in specifications :";
// boolean first = true;
// for (int i = methods.indexOf(m); i < methods.size(); i++) {
// Method element = (Method) methods.elementAt(i);
// if (first) {
// first = false;
// error += " " + element.getName();
// } else
// error += " -> " + element.getName();
// }
// error += " -> " + m.getName();
// throw new PogException(error, this);
// }
//
// // The method parameters are converted.
// // param is the set of converted parameter formula
// // p is the result of the convertion, it possibly corresponds to a
// // context
// Vector param = null;
// ContextFromPureMethod p = null;
// if (right != null) {
// p = right.exprToContextForm(config, methods, false);
// param = p.getFormula().toVector();
// }
//
// // Adds the method to the already met method set.
// methods.add(m);
//
// ContextFromPureMethod c;
//
// if (f.getNodeType() == EQUALITY_OP && f.getNodeText().equals("==")
// && ((BinaryExp) f).getLeft().getNodeType() == T_RESULT) {
// if (instance != null)
// f.instancie(instance);
// // The ensures of the method match with \result == a.
// if (param == null)
// c = new ContextFromPureMethod(((BinaryExp) f).getRight().exprToForm(config,
// methods, pred));
// else
// c = new ContextFromPureMethod(p, ((BinaryExp)
// f).getRight().exprToForm(config, methods, pred)
// .renameParam((Parameters) m.getParams(), param));
// } else {
// m.setPureMethodUsed(true);
// if (param == null) {
// // f = f.subResult(ww);
// // if (instance != null)
// // f.instancie(instance);
// c = new ContextFromPureMethod(ww, pred ? (Formula) new
// BinaryForm(Ja_EQUALS_OP, new TerminalForm(ww),
// new TerminalForm(Ja_LITERAL_true)) : (Formula) new TerminalForm(ww),
// m.getReturnType(),
// //f.exprToForm(config, methods, true)
// new MethodCallForm(m,null,instance != null ? instance.exprToForm(config,
// methods, false) : null,ww));
// } else {
// // f = f.subResult(ww);
// // if (instance != null)
// // f.instancie(instance);
// // Formula f1 = f.exprToForm(config, methods,
// true).renameParam(m.getParams(), param);
//
// c = new ContextFromPureMethod(p, ww, pred ? (Formula) new
// BinaryForm(Ja_EQUALS_OP,
// new TerminalForm(ww), new TerminalForm(Ja_LITERAL_true)) : (Formula) new
// TerminalForm(ww), m
// .getReturnType(),
// new MethodCallForm(m,p.getFormula(),instance != null ?
// instance.exprToForm(config, methods, false) : null,ww)
// //f1
// );
// }
// }
//
// // Removes the method from the already met method set.
// methods.remove(m);
//
// return c;
// }
//
// public String toJava(int indent) {
// return left.toJava(indent) + "(" + (right == null ? "" :
// right.toJava(indent)) + ")";
// }
//
// public AST parse(AST tree) throws Jml2bException {
// // @ set parsed = true;
// AST subtree;
// setNodeType(tree.getType());
// setNodeText(tree.getText());
// setNodeType(MyToken.METHOD_CALL);
// left = Expression.createE(getJmlFile(), tree.getFirstChild());
// subtree = left.parse(tree.getFirstChild());
// if (subtree != null) {
// right = Expression.createE(getJmlFile(),
// tree.getFirstChild().getNextSibling());
// right.parse(tree.getFirstChild().getNextSibling());
// }
// return tree.getNextSibling();
// }
//
// public LinkInfo linkStatement(IJml2bConfiguration config, LinkContext f)
// throws Jml2bException {
// LinkInfo result;
//
// // create a new vector for holding the parameters
// Vector parameters = new Vector();
//
// // if no parameters to method, right == null.
// if (right != null) {
// right.linkParameters(config, f, parameters);
// }
// // left = a gauche de la parenthese
// result = left.linkMethod(config, f, parameters);
//
// // le type d'un noeud method_call correspond au type de
// // retour de la m?thode appell?e
// if (result != null) {
// setStateType(result.getType());
// } else {
// setStateType(null);
// }
//
// return result;
// }
//
// public Type typeCheck(IJml2bConfiguration config, LinkContext f) throws
// Jml2bException {
// if (right != null) {
// right.typeCheck(config, f);
// }
// left.typeCheck(config, f);
// return getStateType();
// }
//
// public void processIdent() {
// left.processIdent();
// if (right != null)
// right.processIdent();
// }
//
// public void isModifiersCompatible(IJml2bConfiguration config, Modifiers
// modifiers) throws LinkException {
// left.isModifiersCompatible(config, modifiers);
// if (right != null)
// right.isModifiersCompatible(config, modifiers);
// }
//
// public JmlExpression instancie() {
// left = (Expression) left.instancie();
// if (right != null)
// right = (Expression) right.instancie();
// return this;
// }
//
// public Expression subField(Field f, Field newF) {
// right = (right == null ? null : right.subField(f, newF));
// return this;
// }
//
// public Expression subResult(String ww) {
// left = (Expression) left.subResult(ww);
// right = (right == null ? null : right.subResult(ww));
// return this;
// }
//
// public JmlExpression instancie(Expression b) {
// left = (Expression) left.instancie(b);
// right = (right == null ? null : (Expression) right.instancie(b));
// return this;
// }
//
// public Vector getParsedItems() {
// Vector res = left.getParsedItems();
// if (right != null)
// res.addAll(right.getParsedItems());
// res.add((ParsedItem) this);
// return res;
// }
//
// public void setParsedItem(ParsedItem pi) {
// left.setParsedItem(pi);
// if (right != null)
// right.setParsedItem(pi);
// change(pi);
// }
//
// public boolean isConstant() {
// return false;
// }
//
// public int getValue() {
// throw new jml2b.exceptions.InternalError("getValue called for non constant
// expression");
// }
//
// // Vector getFreshVars() {
// // Vector res = left.getFreshVars();
// // if (right != null)
// // res.addAll(right.getFreshVars());
// // return res;
// // }
//
// public void old() {
// left.old();
// if (right != null)
// right.old();
// }
//
// public Proofs wp(IJml2bConfiguration config, String result, Proofs
// normalBehaviour,
// ExceptionalBehaviourStack exceptionalBehaviour) throws Jml2bException,
// PogException {
//
// // xx contains the object on witch the method is called.
// String xx = fresh();
//
// // m is the called method.
// AMethod m;
//
// // methodName is the expression corresponding to the method
// // name. It is usefull for coloration
// Expression methodName;
//
// switch (left.getNodeType()) {
// case DOT :
// m = ((TerminalExp) ((BinaryExp) left).getRight()).getIdent().mth;
// methodName = ((BinaryExp) left).getRight();
// break;
// case IDENT :
// case LITERAL_super :
// case LITERAL_this :
// m = ((TerminalExp) left).getIdent().mth;
// methodName = left;
// break;
// default :
// throw new jml2b.exceptions.InternalError("MethodCallExp.wp : bad node type in
// METHOD_CALL "
// + left.getNodeType());
// }
//
// // ww represents the result of the operation call.
// String ww = freshResult(m.getName());
//
// // formalParam is a vector of String
// Vector formalParam = renamedParam(m.getParams());
//
// Expression requires1 = (Expression) m.getNormalizedRequires(config).clone();
//
// // Proof obligations corresponding to the precondition of the
// // called operation.
// SimpleLemma requires = new SimpleLemma(config, (Expression)
// requires1.instancie(new TerminalExp(xx, new Type(m
// .getDefiningClass()))), new GoalOrigin(GoalOrigin.REQUIRES, m));
// Proofs requires2 = new Proofs(requires);
// requires2.addBox(new ColoredInfo(methodName, ColoredInfo.METHOD_CALL,
// m.getInfo(ww)));
// requires2 = requires2.renameParam(m.getParams(), formalParam);
//
// Proofs res = new Proofs();
//
// // Loop on all the cases in the specification of the called
// // method.
// Enumeration e = m.getSpecCases(config);
// while (e.hasMoreElements()) {
// SpecCase sc = (SpecCase) e.nextElement();
// Proofs scp = null;
//
// // Adds coloration to the normal behaviour
// if (m.getReturnType() != null && m.getReturnType().getTag() != Type.T_VOID) {
// scp = ((Proofs) normalBehaviour.clone())./*
// * addBox( new
// * ColoredInfo(left)).
// */sub(new SubTmpVar(result, new TerminalForm(ww)));
// } else {
// scp = ((Proofs) normalBehaviour.clone())/*
// * .addBox( new
// * ColoredInfo(left))
// */;
// }
//
// // Instancie and rename the parameter in the requires of the case
// Expression specRequires = (Expression) sc.getRequires().clone();
// specRequires.old();
// Formula specRequires1 = specRequires.instancie(new TerminalExp(xx, new
// Type(m.getDefiningClass())))
// .predToForm(config);
// specRequires1 = specRequires1.renameParam(m.getParams(), formalParam);
//
// // Instancie and rename the parameter in the ensures of the case
// Expression ensures1 = (Expression) sc.getEnsures().clone();
// ensures1.old();
// // Vector freshVars = ensures1.getFreshVars();
// Formula ensures = ensures1.instancie(new TerminalExp(xx, new
// Type(m.getDefiningClass())))
// .predToForm(config);
// ensures = ensures.renameParam(m.getParams(), formalParam);
//
// // Instancie and rename the parameter in the exsures of the case
// Theorem localExsures = new Theorem(config, sc.getExsures(), new
// TerminalExp(xx, new Type(m
// .getDefiningClass())), new GoalOrigin(GoalOrigin.EXSURES, m));
// localExsures.renameParam(m.getParams(), formalParam);
//
// // Proof obligation corresponding to the proof of the exceptional
// // behavior.
// Proofs exsures = localExsures.impliesExceptional(exceptionalBehaviour);
//
// exsures.addBox(new ColoredInfo(methodName, ColoredInfo.THROWS_EXCEPTION));
// exsures.addBox(new ColoredInfo(methodName, ColoredInfo.METHOD_CALL,
// m.getInfo()));
//
// // Instancie and rename the parameter in the modifies of the case
// ModifiesClause modifies1 = sc.getModifies();
// ModifiesClause modifies = null;
// if (modifies1 != null) {
// modifies = (ModifiesClause) modifies1.clone();
// modifies.instancie(new TerminalExp(xx, new Type()), config);
// if (m.getParams() instanceof Parameters)
// modifies = modifies.renameParam(config, (Parameters) m.getParams(),
// formalParam);
// }
//
// if (m.getReturnType() != null && m.getReturnType().getTag() != Type.T_VOID) {
// // The method returns a value
//
// // Adds the ensures in hypothesis to the normal behaviour
// scp.addHyp( ensures.sub(new TerminalForm(Jm_T_RESULT, "\result"), new
// TerminalForm(ww), false),
// new ColoredInfo(methodName, ColoredInfo.METHOD_CALL, m.getInfo()),// new
// // ColoredInfo(m),
// VirtualFormula.ENSURES);
//
// // Quantifies on the returned value
// scp = scp.quantify(ww, m.getReturnType(), new ColoredInfo(methodName,
// ColoredInfo.METHOD_CALL, m
// .getInfo(ww)));
// } else {
// // Adds the ensures in hypothesis to the normal behaviour
// scp.addHyp( ensures,
// new ColoredInfo(methodName, ColoredInfo.METHOD_CALL, m.getInfo()),
// VirtualFormula.ENSURES);
// }
//
// // Adds the proof of the exceptional behaviour
// scp.addAll(exsures);
//
// if (modifies != null)
// scp = modifies.modifies(config, m, scp);
//
// // Adds the requires of the case in hypothesis
// scp.addHyp(specRequires1, new ColoredInfo(m), VirtualFormula.ENSURES);
// res.addAll(scp);
// }
//
// res.suppressSpecialOld(IFormToken.T_CALLED_OLD);
// // res = res.declareFreshVars(freshVars, ww);
// res.addAll(requires2);
//
// // evaluate the parameter
// res = res.param(config, formalParam, right, exceptionalBehaviour);
//
// if (left.getNodeType() == DOT && !m.getModifiers().isStatic()) {
// Formula s = new BinaryForm(Ja_EQUALS_OP, new TerminalForm(xx), new
// TerminalForm(Ja_LITERAL_null, "null"));
// Formula t = new UnaryForm(Ja_LNOT, s);
// Expression instance = ((BinaryExp) left).getLeft();
//
// if (instance.getNodeType() == LITERAL_this || m.isConstructor())
// res = instance.wp(config, xx, res, exceptionalBehaviour);
// else {
// res.addHyp(t, new ColoredInfo(instance), VirtualFormula.LOCALES);
// Proofs lv = exceptionalBehaviour.throwException(config,
// nullPointerException);
// lv.addHyp(s, new ColoredInfo(instance, ColoredInfo.IS_NULL),
// VirtualFormula.LOCALES);
// res.addAll(lv);
//
// res = instance.wp(config, xx, res, exceptionalBehaviour);
// }
// }
// res.gc(config, true);
// return res;
// }
//
// /**
// * Returns the expression corresponding to the called method.
// *
// * @return <code>left</code>
// */
// public Expression getLeft() {
// return left;
// }
//
// static final long serialVersionUID = 7743883423438724253L;
//
// public void getPrecondition(IJml2bConfiguration config, ModifiableSet
// modifies, Vector req, Vector ens)
// throws Jml2bException, PogException {
// if (right != null)
// right.getPrecondition(config, modifies, req, ens);
//
// Method m;
//
// switch (left.getNodeType()) {
// case DOT :
// m = (Method) ((TerminalExp) ((BinaryExp) left).getRight()).getIdent().mth;
// break;
// case IDENT :
// case LITERAL_super :
// case LITERAL_this :
// m = (Method) ((TerminalExp) left).getIdent().mth;
// break;
// default :
// throw new jml2b.exceptions.InternalError("BinaryExp.getPrecondition : bad
// node type in METHOD_CALL "
// + left.getNodeType());
// }
// if (m == null)
// throw new jml2b.exceptions.InternalError("BinaryExp.getPrecondition : null
// method " + left.toJava(0));
// if (!m.isAnnotated())
// m.annotate(config);
// Vector pre = m.getAnnotatedPrecondition();
// Enumeration e = pre.elements();
// while (e.hasMoreElements()) {
// Expression element = (Expression) e.nextElement();
// Set s = new HashSet();
// element.getFreeVariable(s);
// if (!modifies.containsOne(s))
// req.add(element);
// }
// Vector newEns = new Vector();
// e = ens.elements();
// while (e.hasMoreElements()) {
// Expression element = (Expression) e.nextElement();
// Set s = new HashSet();
// element.getFreeVariable(s);
// ModifiableSet ms = new ModifiableSet(m.getAnnotatedModifies());
// if (!ms.containsOne(s))
// newEns.add(element);
//
// }
// newEns.addAll(m.getAnnotatedPostcondition());
// ens.removeAllElements();
// ens.addAll(newEns);
// modifies.addAll(m.getAnnotatedModifies());
// }
//
// public void collectCalledMethod(Vector calledMethod) {
// switch (left.getNodeType()) {
// case DOT :
// calledMethod.add(((TerminalExp) ((BinaryExp)
// left).getRight()).getIdent().mth);
// break;
// case IDENT :
// case LITERAL_super :
// case LITERAL_this :
// calledMethod.add(((TerminalExp) left).getIdent().mth);
// break;
// default :
// throw new jml2b.exceptions.InternalError("BinaryExp.getPrecondition : bad
// node type in METHOD_CALL "
// + left.getNodeType());
// }
// }
//
// void getFreeVariable(Set s) {
// }
// /**
// * @return
// */
// public Expression getRight() {
// return right;
// }
//
// }

//	public FormulaWithPureMethodDecl getModelThing(ArrayList al, FormulaWithPureMethodDecl mainF, ModifiesClause clause) {
//	
//		boolean modelElements = false;
//		
//		Vector modelFields = new Vector();
//		Vector newModelFields = new Vector();
//		Iterator e = al.iterator();
//	while (e.hasNext()) {
//		AField f = (AField) e.next();
//		if (f.getModifiers().isModel()) {
//			if (f.getType().isArray())
//				modelElements = true;
//			modelFields.add(f);
//			TerminalForm newF = new ModifiedFieldForm(f, clause.getFields());
//			newModelFields.add(newF);
//			mainF =
//				mainF.sub(
//					new TerminalForm(new Identifier(f)),
//					newF,
//					true);
//		}
//	}
//	
//		TerminalForm[] newModifiedElements = null;
//	
//		if (modelElements) {
//			newModifiedElements =
//				new TerminalForm[ElementsForm.elements.length];
//			for (int i = 0; i < ElementsForm.elements.length; i++) {
//				newModifiedElements[i] =
//					new ElementsForm(ElementsForm.elements[i]);
//				mainF =
//					mainF.sub(
//						ElementsForm.elements[i],
//						newModifiedElements[i],
//						true);
//			}
//		}
//	
//	
//	
//	//	mainF = main.getFormula();
//	
//		e = al.iterator();
////		Enumeration e1 = newModelFields.elements();
//		while (e.hasNext()) {
//			AField f = (AField) e.next();
//			
////			TerminalForm newF = (TerminalForm) e1.nextElement();
//			if (f.getModifiers().isStatic()) {
////				mainF =
////					new FormulaWithPureMethodDecl(mainF,
////					new QuantifiedForm(
////						Jm_EXISTS,
////						new QuantifiedVarForm(
////							f,
////							new TTypeForm(
////								IFormToken.T_TYPE,
////								f.getType())),
////						mainF.getFormula()));
//			} else {
////				mainF =
////					new FormulaWithPureMethodDecl(mainF,
////					new QuantifiedForm(
////						Jm_EXISTS,
////						new QuantifiedVarForm(
////							newF,
////							new BinaryForm(
////								IS_MEMBER_FIELD,
////								new TTypeForm(
////									IFormToken.T_TYPE,
////									new Type(f.getDefiningClass())),
////								new TTypeForm(
////									IFormToken.T_TYPE,
////									f.getType()))),
////						mainF.getFormula()));
//			} //else {
//			//						mainF =
//			//							new QuantifiedForm(
//			//								Jm_EXISTS,
//			//								new QuantifiedVarForm(
//			//									newF,
//			//									new BinaryForm(
//			//										B_PARTIALFUNCTION,
//			//										TerminalForm.REFERENCES,
//			//										TerminalForm.REFERENCES)),
//			//								mainF);
//			//					}
//		}
//	
//		if (modelElements)
//			for (int i = 0; i < ElementsForm.elements.length; i++) {
//				mainF =
//					new FormulaWithPureMethodDecl(mainF,
//					new QuantifiedForm(
//						Jm_EXISTS,
//						new QuantifiedVarForm(
//							newModifiedElements[i],
//							ElementsForm.elements[i].getType()),
//						mainF.getFormula()));
//			}
//		return mainF;
//	}
//
//}