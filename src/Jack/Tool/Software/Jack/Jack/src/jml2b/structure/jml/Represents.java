//******************************************************************************
/* Copyright (c) 2002, 2003 GEMPLUS Software Research Labs. All Rights Reserved.
/* Copyright (c) 2003, 2004 INRIA. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: Represents
/*
/*******************************************************************************
/* Warnings/Remarks:
/******************************************************************************/
package jml2b.structure.jml;

import java.util.Vector;

import jml.LineAST;
import jml2b.IJml2bConfiguration;
import jml2b.exceptions.Jml2bException;
import jml2b.exceptions.TokenException;
import jml2b.link.LinkContext;
import jml2b.structure.java.Class;
import jml2b.structure.java.Declaration;
import jml2b.structure.java.IModifiers;
import jml2b.structure.java.JmlFile;
import jml2b.structure.java.Modifiers;
import jml2b.structure.java.ParsedItem;
import jml2b.structure.java.Type;
import jml2b.structure.statement.Expression;
import jml2b.structure.statement.MyToken;
import antlr.collections.AST;

/**
 * This abstract class describes a <i>represents</i> clause.
 * @author L. Burdy
 **/
public abstract class Represents extends Declaration implements JmlExpression {

	/**
	 * Creates an empty represent clause from a loaded file.
	 * @param jf The Jml file where the clause is defined
	 * @param tree The AST tree representing the clause
	 * @param m The modifiers associated with the clause
	 * @param defining The defining class.
	 **/
	public static Represents create(
		JmlFile jf,
		AST tree,
		IModifiers m,
		Class defining)
		throws Jml2bException {
		switch (tree.getType()) {
			case L_ARROW :
				return new RepresentsArrow(jf, tree, m, defining);
			case T_SUCH_THAT :
				return new RepresentsSuchThat(jf, tree, m, defining);
			default :
				throw new TokenException(
					jf,
					(LineAST) tree,
					"Represents.create",
					"declaration token",
					MyToken.nodeString[tree.getType()]
						+ "("
						+ tree.getType()
						+ ")");
		}
	}

	/**
	 * The variable that is glued.
	 **/
	private Modifies depend;

	/**
	 * The gluing invariant that can be a direct glue or a property.
	 **/
	private Expression gluingInvariant;

	/**
	 * Constructs a represents clause from another one
	 * @param pi The corresponding parsed item
	 * @param mod The modifiers
	 * @param m The model variable
	 * @param e The glue
	 **/
	/*@
	  @ requires m != null && e != null;
	  @*/
	Represents(ParsedItem pi, IModifiers mod, Modifies m, Expression e) {
		super(pi, mod);
		depend = m;
		gluingInvariant = e;
	}

	/**
	 * Constructs an empty represent clause from a loaded file.
	 * @param jf The Jml file where the clause is defined
	 * @param tree The AST tree representing the clause
	 * @param m The modifiers associated with the clause
	 * @param defining The defining class.
	 **/
	/*@
	  @ requires m != null;
	  @*/
	public Represents(JmlFile jf, AST tree, IModifiers m, Class defining) {
		super(jf, tree, m, defining);
	}

	public abstract Object clone();

	/*@
	  @ requires ast != null;
	  @ requires typeof(ast) <: \type(LineAST);
	  @ modifies invariant;
	  @*/
	public AST parse(JmlFile jmlFile, AST ast) throws Jml2bException {
		//@ set parsed = true;
		depend = Modifies.create(jmlFile, ast.getFirstChild());
		gluingInvariant =
			Expression.createE(jmlFile, ast.getFirstChild().getNextSibling());
		gluingInvariant.parse(ast.getFirstChild().getNextSibling());
		return null;
	}

	/*@
	  @ requires parsed;
	  @*/
	public final void link(IJml2bConfiguration config, LinkContext f)
		throws Jml2bException {
	}

	/*@
	  @ requires parsed;
	  @*/
	public int linkStatements(IJml2bConfiguration config, LinkContext f)
		throws Jml2bException {
		depend.linkStatements(config, f);
		gluingInvariant.linkStatements(config, f);
		return 0;
	}

	public Type typeCheck(IJml2bConfiguration config, LinkContext f)
		throws Jml2bException {
		depend.typeCheck(config, f);
		gluingInvariant.typeCheck(config, f);
		return null;
	}

	public JmlExpression instancie() {
		depend = depend.instancie();
		gluingInvariant = (Expression) gluingInvariant.instancie();
		return this;
	}

	public JmlExpression instancie(Expression b) {
		depend.instancie(b);
		gluingInvariant = (Expression) gluingInvariant.instancie(b);
		return this;
	}

	public final Vector getParsedItems() {
		Vector res = depend.getParsedItems();
		res.addAll(gluingInvariant.getParsedItems());
		return res;
	}

	/**
	 * @return <code>null</code>
	 **/
	public final String getName() {
		return null;
	}

	/**
	 * Returns the depends.
	 * @return <code>depend</code>
	 */
	public Modifies getDepend() {
		return depend;
	}

	/**
	 * Returns the gluing invariant.
	 * @return <code>gluingInvariant</code>
	 */
	public Expression getGluingInvariant() {
		return gluingInvariant;
	}


}