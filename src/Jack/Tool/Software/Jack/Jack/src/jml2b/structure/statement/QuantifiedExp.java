//******************************************************************************
/* Copyright (c) 2002, 2003 GEMPLUS Software Research Labs. All Rights Reserved.
/* Copyright (c) 2003, 2004 INRIA. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: QuantifiedExp.java
/*
/*******************************************************************************
/* Warnings/Remarks:
/******************************************************************************/
package jml2b.structure.statement;

import java.util.Set;
import java.util.Vector;

import jml.JmlDeclParserTokenTypes;
import jml2b.IJml2bConfiguration;
import jml2b.exceptions.Jml2bException;
import jml2b.exceptions.LinkException;
import jml2b.exceptions.PogException;
import jml2b.formula.BinaryForm;
import jml2b.formula.Formula;
import jml2b.formula.IFormToken;
import jml2b.formula.QuantifiedForm;
import jml2b.formula.QuantifiedVarForm;
import jml2b.formula.TTypeForm;
import jml2b.formula.TerminalForm;
import jml2b.formula.UnaryForm;
import jml2b.link.LinkContext;
import jml2b.link.LinkInfo;
import jml2b.pog.lemma.ExceptionalBehaviourStack;
import jml2b.pog.lemma.FormulaWithSpecMethodDecl;
import jml2b.pog.lemma.Proofs;
import jml2b.pog.substitution.SubTmpVar;
import jml2b.pog.util.ColoredInfo;
import jml2b.structure.java.Field;
import jml2b.structure.java.Identifier;
import jml2b.structure.java.JmlFile;
import jml2b.structure.java.Modifiers;
import jml2b.structure.java.ParsedItem;
import jml2b.structure.java.Type;
import jml2b.structure.jml.JmlExpression;
import jml2b.util.ModifiableSet;
import antlr.collections.AST;

/**
 * This class implements a quantified expression, that is 
 * <code>\forall type var; body</code> or <code>\exists type var; body</code>.
 * The node text can be respectively "!" or "#".
 * @author L. Burdy
 **/
public class QuantifiedExp extends Expression {

	/**
	 * The list of quantified variable
	 **/
	private QuantifiedVar vars;

	/**
	 * The quantified expression
	 **/
	private Expression body;

	/*@
	  @ invariant parsed ==> vars != null
	  @        && parsed ==> body != null
	  @        && parsed ==> body.parsed;
	  @*/

	/**
	 * Constructs an expression as a <i>parsed item</i>.
	 * @param jf The file where the statement is located
	 * @param tree The <code>AST</code> node corresponding to the statement
	 * @see jml2b.structure.java.ParsedItem#ParsedItem(JmlFile, AST)
	 **/
	QuantifiedExp(JmlFile jf, AST tree) {
		super(jf, tree);
	}

	/**
	 * Constructs a quantified expression form another one
	 * @param nodeType The node type
	 * @param nodeText The node text
	 * @param vars The quantified variables
	 * @param body he quantified expression
	 **/
	/*@
	  @ requires vars != null && body != null;
	  @*/
	public QuantifiedExp(
		int nodeType,
		String nodeText,
		QuantifiedVar vars,
		Expression body) {
		super(nodeType, nodeText);
		this.vars = vars;
		this.body = body;
		//@ set parsed = true;
	}

	public Object clone() {
		QuantifiedExp res =
			new QuantifiedExp(
				getNodeType(),
				getNodeText(),
				(QuantifiedVar) vars.clone(),
				(Expression) body.clone());
		res.setBox(this);
		res.setStateType(getStateType());
		//@ set res.parsed = true;
		return res;
	}

	public boolean equals(Expression e) {
		return getNodeType() == e.getNodeType()
			&& vars.equals(((QuantifiedExp) e).vars)
			&& body.equals(((QuantifiedExp) e).body);
	}

	/**
	 * <code>\forall type var; body</code> is converted identically when type is
	 * builtin or into <code>\forall REFERENCES var; (var != null ==>
	 * \typeof(var) <: type) ==> body</code> if not. The same conversion applies
	 * for <code>\exists type var; body</code>.
	 **/
	FormulaWithSpecMethodDecl exprToContextForm(
		IJml2bConfiguration config,
		Vector methods,
		boolean pred)
		throws Jml2bException, PogException {
		Formula res;
		QuantifiedVar v = vars;
		QuantifiedVarForm w = null;
		FormulaWithSpecMethodDecl b = body.exprToForm(config, methods, true);

		while (v != null) {
			if (v.getField().getType().isBuiltin())
				w =
					new QuantifiedVarForm(
						new TerminalForm(new Identifier(v.getField())),
						new TTypeForm(
							IFormToken.T_TYPE,
							v.getField().getType()),
						w);
			else {
				w =
					new QuantifiedVarForm(
						new TerminalForm(new Identifier(v.getField())),
						TerminalForm.$References,
						w);

				// b = (v != null ==> \typeof(v) <: type) ==> b 
				b =
					new FormulaWithSpecMethodDecl(b,
					new BinaryForm(
						Jm_IMPLICATION_OP,
						new BinaryForm(
							Jm_IMPLICATION_OP,
							new BinaryForm(
								Ja_DIFFERENT_OP,
								new TerminalForm(new Identifier(v.getField())),
								new TerminalForm(Ja_LITERAL_null, "null")),
							new BinaryForm(
								Jm_IS_SUBTYPE,
								new BinaryForm(
									IFormToken.B_APPLICATION,
									TerminalForm.$typeof,
									new TerminalForm(
										new Identifier(v.getField()))),
								new TTypeForm(
									IFormToken.Jm_T_TYPE,
									v.getField().getType()))),
						b.getFormula()));
			}
			v = v.getNext();
		}
		res =
			new QuantifiedForm(
				getNodeText().equals("!") ? Jm_FORALL : Jm_EXISTS,
				w,
				b.getFormula());
		if (!pred)
			res = new UnaryForm(B_BOOL, res);

		return new FormulaWithSpecMethodDecl(b, res);
	}

	public String toJava(int indent) {
		String r =
			"("
				+ (getNodeText().equals("!") ? "\\forall " : "\\exists ")
				+ vars.toJava()
				+ ";";
		return r + body.toJava(indent + r.length()) + ")";
	}

	public AST parse(AST tree) throws Jml2bException {
		setNodeType(QUANTIFIED_EXPR);
		if (tree.getFirstChild().getText().equals("\\forall"))
			setNodeText("!");
		else
			setNodeText("#");
		vars =
			new QuantifiedVar(
				getJmlFile(),
				tree.getFirstChild().getNextSibling().getFirstChild());
		body =
			Expression.createE(
				getJmlFile(),
				tree.getFirstChild().getNextSibling().getNextSibling());
		body.parse(tree.getFirstChild().getNextSibling().getNextSibling());
		if (tree
			.getFirstChild()
			.getNextSibling()
			.getNextSibling()
			.getNextSibling()
			!= null) {
			Expression body1 =
				Expression.createE(
					getJmlFile(),
					tree
						.getFirstChild()
						.getNextSibling()
						.getNextSibling()
						.getNextSibling());
			body1.parse(
				tree
					.getFirstChild()
					.getNextSibling()
					.getNextSibling()
					.getNextSibling());
			body =
				new BinaryExp(
					JmlDeclParserTokenTypes.IMPLICATION_OP,
					body,
					"==>",
					body1);

		}
		//@ set parsed = true;
		return tree.getNextSibling();
	}

	public LinkInfo linkStatement(IJml2bConfiguration config, LinkContext f)
		throws Jml2bException {
		setStateType(Type.getBoolean());
		// create new local variables
		f.linkVars.pushVars();
		vars.linkStatement(config, f);
		body.linkStatement(config, f);
		// remove the local variables
		f.linkVars.popVars();
		return new LinkInfo(getStateType());
	}

	public Type typeCheck(IJml2bConfiguration config, LinkContext f)
		throws Jml2bException {
		body.typeCheck(config, f);
		return Type.getBoolean();

	}

	public void processIdent() {
		vars.processIdent();
		body.processIdent();
	}

	public void isModifiersCompatible(IJml2bConfiguration config, Modifiers modifiers)
		throws LinkException {
		body.isModifiersCompatible(config, modifiers);
	}

	public JmlExpression instancie() {
		body = (Expression) body.instancie();
		return this;
	}

	public JmlExpression instancie(Expression b) {
		body = (Expression) body.instancie(b);
		return this;
	}

	public Expression subField(Field f, Field newF) {
		body = body.subField(f, newF);
		return this;
	}

	public Expression subResult(String ww) {
		body = body.subResult(ww);
		return this;
	}

	public Vector getParsedItems() {
		Vector res = vars.getParsedItems();
		res.addAll(body.getParsedItems());
		res.add((ParsedItem) this);
		return res;
	}

	public void setParsedItem(ParsedItem pi) {
		vars.setParsedItem(pi);
		body.setParsedItem(pi);
		change(pi);
	}

	public boolean isConstant() {
		return false;
	}

	Vector getFreshVars() {
		return new Vector();
	}

	public void old() {
		body.old();
	}

	/**
	 * @throws InternalError since this expression is a JML expression
	 **/
	public Proofs wp(
		IJml2bConfiguration config,
		String result,
		Proofs normalProof,
		ExceptionalBehaviourStack exceptionalProof)
		throws Jml2bException, PogException {
		String v2 = fresh();
		Formula s =
			new QuantifiedExp(
				getNodeType(),
				getNodeText(),
				vars,
				new TerminalExp(v2, Type.getBoolean())).exprToForm(
				config).getFormula();
		return body.wp(
			config,
			v2,
			((Proofs) normalProof.clone()).addBox(new ColoredInfo(this)).sub(
				new SubTmpVar(result, s)),
			exceptionalProof);
	}

	static final long serialVersionUID = 3537501373084566514L;

	public void getPrecondition(
		IJml2bConfiguration config,
		ModifiableSet modifies,
		Vector req,
		Vector ens) {
	}

	public void collectCalledMethod(Vector calledMethod) {
	}

	void getFreeVariable(Set s) {
		body.getFreeVariable(s);
	}

	/**
	 * @return
	 */
	public Expression getBody() {
		return body;
	}

	/**
	 * @return
	 */
	public QuantifiedVar getVars() {
		return vars;
	}

}
