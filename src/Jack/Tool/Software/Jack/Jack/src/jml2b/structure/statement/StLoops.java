//******************************************************************************
/* Copyright (c) 2002, 2003 GEMPLUS Software Research Labs. All Rights Reserved.
/* Copyright (c) 2003, 2004 INRIA. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: StLoops.java
/*
/*******************************************************************************
/* Warnings/Remarks:
/*  09/26/2003 : Simplify integration achieved
/******************************************************************************/
package jml2b.structure.statement;

import java.util.Enumeration;
import java.util.Vector;

import jml.LineAST;
import jml2b.IJml2bConfiguration;
import jml2b.exceptions.Jml2bException;
import jml2b.exceptions.LinkException;
import jml2b.exceptions.ParseException;
import jml2b.exceptions.PogException;
import jml2b.exceptions.TokenException;
import jml2b.formula.IModifiesField;
import jml2b.link.LinkContext;
import jml2b.link.LinkInfo;
import jml2b.link.LinkUtils;
import jml2b.pog.lemma.ExceptionalBehaviourStack;
import jml2b.pog.lemma.Proofs;
import jml2b.pog.lemma.Theorem;
import jml2b.structure.java.Class;
import jml2b.structure.java.JmlFile;
import jml2b.structure.java.Method;
import jml2b.structure.java.Type;
import jml2b.structure.jml.Exsures;
import jml2b.structure.jml.ModifiesClause;
import jml2b.structure.jml.ModifiesList;
import jml2b.structure.jml.SpecCase;
import jml2b.util.StatementUtils;
import antlr.collections.AST;

/**
 * This abstract class implements a loop statement.
 * @author L. Burdy
 **/
public abstract class StLoops extends Statement implements IModifiesField {

	/**
	 * Parses an ensures clause.
	 * @param jmlFile The currently parsed file
	 * @param a The current AST node
	 * @return the set of ensures clause as expressions
	 **/
	/*@
	  @ ensures \result != null
	  @      && \result.elementType <: \type(Expression)
	  @*/
	private static Vector parseEnsures(JmlFile jmlFile, AST a)
		throws Jml2bException {
		Vector res = new Vector();
		while (a != null) {
			if (a.getType() != MAINTAINING_KEYWORD) {
				throw new TokenException(
					jmlFile,
					(LineAST) a,
					"Statement.parseEnsures",
					"MAINTAINING_KEYWORD",
					a.getType());
			}

			Expression s = Expression.createE(jmlFile, a.getFirstChild());
			s.parse(a.getFirstChild());
			res.add(s);

			a = a.getNextSibling();
		}
		return res;
	}

	/**
	 * The node type of the loop. It can be <code>LITERAL_for</code>, 
	 * <code>LITERAL_do</code> or <code>LITERAL_while</code>
	 **/
	private int nodeType;

	/**
	 * The body of the loop
	 **/
	protected Statement body;
	
	/**
	 * The loop invariant
	 **/
	private Expression loop_invariant;

	/**
	 * The loop variant
	 **/
	private Expression loop_variant;

	/**
	 * The loop modifies clause
	 **/
	private ModifiesClause loop_modifies;

	/**
	 * The loop exsures clause
	 **/
	private Vector loop_exsures;

	protected int line;

	/*@
	  @ private invariant nodeType == LITERAL_for
	  @                || nodeType == LITERAL_do
	  @                || nodeType == LITERAL_while;
	  @ private invariant loop_exsures != null 
	  @                && loop_exsures.elementType == \type(Exsures);
	  @ invariant parsed ==> loop_invariant != null;
	  @ invariant parsed ==> loop_modifies != null;
	  @*/

	/**
	 * Constructs a statement as a <i>parsed item</i>.
	 * @param jf The file where the statement is located
	 * @param tree The <code>AST</code> node corresponding to the statement
	 * @see jml2b.structure.java.ParsedItem#ParsedItem(JmlFile, AST)
	 **/
	/*@
	  @ requires tree.getType() == LITERAL_for
	  @       || tree.getType() == LITERAL_do
	  @       || tree.getType() == LITERAL_while;
	  @*/
	StLoops(JmlFile jf, AST tree) {
		super(jf, tree);
		nodeType = tree.getType();
		loop_exsures = new Vector();
		line = ((LineAST) tree).line;
	}

	public LinkInfo linkStatement(IJml2bConfiguration config, LinkContext f)
		throws Jml2bException {
		if (loop_modifies == null) {
			loop_modifies =
				(ModifiesClause) ((Method) f
					.currentMethod)
					.getDefaultLoopModifies()
					.clone();
			if (f.linkVars.elements().hasMoreElements())
				loop_modifies =
					loop_modifies.completeModifiesWithFields(
						new ModifiesList(f.linkVars.elements()));
		} else
			loop_modifies.linkStatements(config, f);
		getLoop_invariant().linkStatement(config, f);
		if (getLoop_variant() == null) {
			int t = ((Method) f
					.currentMethod).getSpecType();
			if (t == SpecCase.NORMAL_BEHAVIOR_CASE
				|| t == SpecCase.EXCEPTIONAL_BEHAVIOR_CASE
				|| t == SpecCase.DEFAULT_BEHAVIOR_CASE)
				throw new LinkException(
					"In methods specified with a behavior, loops must have a decreases clause.",
					this);
		} else
			getLoop_variant().linkStatement(config, f);
		LinkUtils.linkEnumeration(config, getLoop_exsures().elements(), f);
		LinkUtils.linkStatements(config, getLoop_exsures().elements(), f);
		return null;
	}

	public Type typeCheck(IJml2bConfiguration config, LinkContext f)
		throws Jml2bException {
		getLoop_modifies().typeCheck(config, f);
		getLoop_invariant().typeCheck(config, f);
		if (getLoop_variant() != null)
			getLoop_variant().typeCheck(config, f);
		LinkUtils.typeCheckEnumeration(config, getLoop_exsures().elements(), f);
		return null;
	}

	public Statement jmlNormalize(
		IJml2bConfiguration config,
		Class definingClass)
		throws PogException {
		loop_invariant.processIdent();
		loop_invariant = (Expression) loop_invariant.instancie();

		SpecCase.exsureVectorProcessIdent(loop_exsures.elements());
		SpecCase.exsureVectorInstancie(loop_exsures.elements());

		loop_modifies.processIdent();
		loop_modifies.instancie(config);
		loop_modifies.addDepends(config, definingClass);

		return this;
	}

	/**
	 * Parses a modifies clause.
	 * @param jmlFile The currently parsed file
	 * @param a The current AST node
	 * @return the set of ensures clause as expressions
	 **/
	public void parseModifies(JmlFile jmlFile, AST a) throws Jml2bException {
		while (a != null) {
			switch (a.getType()) {
				case LOOP_ASSIGNABLE_KEYWORD :
					ModifiesClause tmp =
						ModifiesClause.create(jmlFile, a.getFirstChild());
					if (tmp != null)
						if (loop_modifies == null) {
							loop_modifies = tmp;
						} else {
							try {
								((ModifiesList) loop_modifies).add(
									(ModifiesList) tmp);
							} catch (ClassCastException cce) {
								throw new ParseException(
									jmlFile,
									(LineAST) a,
									"Invalid modifies clause");
							}
						}
					break;
				default :
					throw new TokenException(
						jmlFile,
						(LineAST) a,
						"StLoops.parseModifies",
						"LOOP_ASSIGNABLE_KEYWORD",
						a.getType());
			}
			a = a.getNextSibling();
		}
	}

	//	public void defaultLoop_modifies() {
	//		loop_modifies = new ModifiesNothing();
	//	}

	/**
	 * Parses a loop invariant clause.
	 * @param subtree The current AST node
	 * @return the set of ensures clause as expressions
	 **/
	public void parseLoopInvariant(AST subtree) throws Jml2bException {
		if (subtree.getFirstChild() != null) {
			loop_invariant =
				StatementUtils.andEnumeration(
					StLoops
						.parseEnsures(getJmlFile(), subtree.getFirstChild())
						.elements());
		} else {
			loop_invariant = new TerminalExp(BTRUE, "(0==0)");
		}
	}

	/**
	 * Parses a loop variant clause.
	 * @param subtree The current AST node
	 * @return the set of ensures clause as expressions
	 **/
	public void parseLoopVariant(AST subtree) throws Jml2bException {
		if (subtree.getFirstChild() != null) {
			loop_variant =
				Expression.createE(
					getJmlFile(),
					subtree.getFirstChild().getFirstChild());
			loop_variant.parse(subtree.getFirstChild().getFirstChild());
		} else
			loop_variant = null;
	}

	/**
	 * Parses an exsures clause.
	 * @param jmlFile The currently parsed file
	 * @param a The current AST node
	 * @return the set of exsures clause
	 **/
	private void parseExsures(JmlFile jmlFile, AST a) throws Jml2bException {
		while (a != null) {
			if (a.getType() != SIGNALS_KEYWORD) {
				throw new TokenException(
					jmlFile,
					(LineAST) a,
					"Statement.parseExsures",
					"SIGNALS_KEYWORD",
					a.getType());
			}

			AST current = a.getFirstChild();
			if (current.getType() != LPAREN) {
				throw new TokenException(
					jmlFile,
					(LineAST) a,
					"Statement.parseExsures",
					"LPAREN",
					current.getType());
			}
			current = current.getNextSibling();
			// parse the type of the exception
			Type ex_type = new Type(jmlFile, current);
			ex_type.parse(current);
			current = current.getNextSibling();

			String ex_name = null;
			if (current.getType() == IDENT) {
				ex_name = current.getText();
				current = current.getNextSibling();
			}
			if (current.getType() != RPAREN) {
				throw new TokenException(
					jmlFile,
					(LineAST) a,
					"Statement.parseExsures",
					"RPAREN",
					current.getType());
			}
			current = current.getNextSibling();
			Expression ex_statement = Expression.createE(jmlFile, current);
			ex_statement.parse(current);

			Exsures exs = new Exsures(ex_type, ex_name, ex_statement);

			loop_exsures.add(exs);

			// next exsures clause
			a = a.getNextSibling();
		}
	}

	/**
	 * Parses a loop exsures clause.
	 * @param subtree The current AST node
	 * @return the set of ensures clause as expressions
	 **/
	public void parseLoopExsures(AST subtree) throws Jml2bException {
		if (subtree.getFirstChild() != null)
			parseExsures(getJmlFile(), subtree.getFirstChild());
	}

	Proofs wellDef(IJml2bConfiguration config)
		throws Jml2bException, PogException {
		if (config.isWellDefPoGenerated()) {
			Proofs res =
				loop_invariant.ensures(
					config,
					Theorem.getTrue(config),
					ExceptionalBehaviourStack.getFalse(config),
					new Vector());
			if (loop_variant != null)
				res.addAll(
					loop_variant.ensures(
						config,
						Theorem.getTrue(config),
						ExceptionalBehaviourStack.getFalse(config),
						new Vector()));
			return res;
		} else
			return new Proofs();
	}

	/**
	 * Returns the loop exsures clause.
	 * @return <code>loop_exsures</code>
	 */
	public Vector getLoop_exsures() {
		return loop_exsures;
	}

	/**
	 * Returns the loop invariant.
	 * @return <code>loop_invariant</code>
	 */
	public Expression getLoop_invariant() {
		return loop_invariant;
	}

	/**
	 * Returns the loop modifies clause.
	 * @return <code>lopp_modifies</code>
	 */
	public ModifiesClause getLoop_modifies() {
		return loop_modifies;
	}

	/**
	 * Returns the node type.
	 * @return <code>nodeType</code>
	 */
	public int getNodeType() {
		return nodeType;
	}

	public String getNameForModifies() {
		return "after loop at line " + line;
	}

	static final long serialVersionUID = -2538988515269093588L;

	/**
	 * @return
	 */
	public Expression getLoop_variant() {
		return loop_variant;
	}

	public String getInfo() {
		String res = "\n";
		if (loop_modifies != null)
			res += " loop_modifies " + loop_modifies.toJava(15) + ";\n";
		if (loop_invariant != null)
			res += " loop_invariant " + loop_invariant.toJava(16) + ";\n";
		Enumeration e = loop_exsures.elements();
		while (e.hasMoreElements()) {
			Exsures ex = (Exsures) e.nextElement();
			res += " exsures " + ex.toJava(9) + ";\n";
		}
		if (loop_variant != null)
			res += " diverges " + loop_variant.toJava(10) + ";\n";
		return res;
	}
	
	public Statement getBody() {
		return body;
	}
	
}

class DuringLoop implements IModifiesField {

	int line;

	DuringLoop(int line) {
		this.line = line;
	}

	public String getNameForModifies() {
		return "during loop at line " + line;
	}

}