//******************************************************************************
/* Copyright (c) 2002, 2003 GEMPLUS Software Research Labs. All Rights Reserved.
/* Copyright (c) 2003, 2004 INRIA. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: StTry.java
/*
/*******************************************************************************
/* Warnings/Remarks:
/******************************************************************************/
package jml2b.structure.statement;

import java.util.Vector;

import jml.JmlDeclParserTokenTypes;
import jml2b.IJml2bConfiguration;
import jml2b.exceptions.Jml2bException;
import jml2b.exceptions.PogException;
import jml2b.link.LinkContext;
import jml2b.link.LinkInfo;
import jml2b.pog.util.IdentifierResolver;
import jml2b.structure.java.Class;
import jml2b.structure.java.Field;
import jml2b.structure.java.JmlFile;
import jml2b.structure.java.ParsedItem;
import jml2b.structure.java.Type;
import antlr.collections.AST;

/**
 * This class implements a list of catch clause
 * @author L. Burdy, A. Requet
 **/
class CatchList extends ParsedItem {

	/** 
	 * The catched exception and its instance stored as a field
	 **/
	private Field catchParam;

	/**
	 * The body of the catch clause
	 **/
	private Statement body;

	/**
	 * The next element of the list
	 **/
	private CatchList next;

	/*@
	  @ ghost boolean parsed = false;
	  @ invariant parsed ==> catchParam != null
	  @        && parsed ==> body != null
	  @        && parsed ==> body.parsed
	  @        && parsed && next != null ==> next.parsed;
	  @*/

	/**
	 * Constructs an empty list corresponding to a parsed item that will be 
	 * filled by the parse.
	 * @param jf The current JML file
	 * @param a The tree corresponding to this modifies
	 **/
	CatchList(JmlFile jf, AST tree) {
		super(jf, tree);
	}


	/**
	 * Parses an <code>AST</code> tree in order to instanciate the fields.
	 * @param tree <code>AST</code> tree containing the statement
	 * @throws Jml2bException when a parse error occurs.
	 **/
	/*@
	  @ modifies catchParam, body, next;
	  @ ensures catchParam != null && body != null;
	  @*/
	AST parse(AST tree) throws Jml2bException {
		AST subtree;
		// The catched exception
		Type catchParamType =
			new Type(getJmlFile(), tree.getFirstChild().getFirstChild());
		subtree = catchParamType.parse(tree.getFirstChild().getFirstChild());

		// The catched parameter described with a field
		catchParam =
			new Field(
				new ParsedItem(getJmlFile(), subtree),
				catchParamType,
				subtree.getText());

		// The body of the catch clause
		body =
			Statement.createS(
				getJmlFile(),
				tree.getFirstChild().getNextSibling());
		subtree = body.parse(tree.getFirstChild().getNextSibling());

		subtree = tree.getNextSibling();
		if (subtree != null
			&& subtree.getType() == JmlDeclParserTokenTypes.LITERAL_catch) {
			// The next element if it exists
			next = new CatchList(getJmlFile(), subtree);
			subtree = next.parse(subtree);
		} else
			next = null;
		//@ set parsed = true;
		return subtree;
	}

	/**
	 * Links the catch parameter, the body and the next element if it exists.
	 * @return the link info resulting from the link
	 * @throws Jml2bException
	 **/
	/*@
	  @ requires parsed;
	  @*/
	LinkInfo linkStatement(IJml2bConfiguration config, LinkContext f)
		throws Jml2bException {
		catchParam.link(config, f);
		catchParam.linkStatements(config, f);

		f.linkVars.pushVars();
		f.linkVars.add(catchParam);

		body.linkStatement(config, f);

		f.linkVars.popVars();

		if (next != null)
			next.linkStatement(config, f);
		return null;
	}

	public void typeCheck(IJml2bConfiguration config, LinkContext f)
		throws Jml2bException {
		f.linkVars.pushVars();
		f.linkVars.add(catchParam);

		body.typeCheck(config, f);

		f.linkVars.popVars();

		if (next != null)
			next.typeCheck(config, f);

	}
	/**
	 * Instancie the statement.
	 * More 
	 * <a href="{@docRoot}/jml2b/structure/statement/doc-files/instancie.html"> 
	 * informations</a> on instancie.
	 * @return the instanciated statement
	 **/
	/*@
	  @ requires parsed;
	  @*/
	CatchList jmlNormalize(IJml2bConfiguration config, Class definingClass)
		throws PogException {
		catchParam.nameIndex = IdentifierResolver.addIdent(catchParam);
		body = (Statement) body.jmlNormalize(config, definingClass);
		if (next != null)
			next = next.jmlNormalize(config, definingClass);
		return this;
	}

	static final long serialVersionUID = 3784255115209090984L;

	/**
	 * @return
	 */
	public Statement getBody() {
		return body;
	}

	/**
	 * @return
	 */
	public CatchList getNext() {
		return next;
	}

}

/**
 * This class implements a try catch finally statement or a try catch or a try
 * finally statement.
 * @author L. Burdy
 **/
public class StTry extends Statement {

	/**
	 * The <code>try</code> statement
	 **/
	private Statement tryTk;

	/**
	 * The list of catch statements, it can be <code>null</code>.
	 **/
	private CatchList catchTk;

	/**
	 * The <code>finally</code> statement, it can be <code>null</code>.
	 **/
	private Statement finallyTk;

	/*@
	  @ invariant parsed ==> tryTk != null
	  @        && parsed ==> tryTk.parsed
	  @        && (parsed && catchTk != null ==> catchTk.parsed)
	  @        && (parsed && finallyTk != null ==> finallyTk.parsed);
	  @*/

	/**
	 * Construct an empty statement that will be filled during the parse
	 * @param jf The JML file
	 * @param tree The current AST tree node
	 **/
	protected StTry(JmlFile jf, AST tree) {
		super(jf, tree);
	}

	/*@
	  @ modifies tryTk, catchTk, finallyTk;
	  @ ensures tryTk != null;
	  @*/
	public AST parse(AST tree) throws Jml2bException {
		tryTk = Statement.createS(getJmlFile(), tree.getNextSibling());
		AST subtree = tryTk.parse(tree.getNextSibling());

		if (subtree.getType() == LITERAL_catch) {
			catchTk = new CatchList(getJmlFile(), subtree);
			subtree = catchTk.parse(subtree);
		} else
			catchTk = null;

		if (subtree != null && subtree.getType() == LITERAL_finally) {
			finallyTk =
				Statement.createS(getJmlFile(), subtree.getNextSibling());
			subtree = finallyTk.parse(subtree.getNextSibling());
		} else
			finallyTk = null;
		//@ set parsed = true;
		return subtree;
	}

	public LinkInfo linkStatement(IJml2bConfiguration config, LinkContext f)
		throws Jml2bException {
		tryTk.linkStatement(config, f);
		if (catchTk != null)
			catchTk.linkStatement(config, f);
		if (finallyTk != null)
			finallyTk.linkStatement(config, f);
		return null;
	}

	public Type typeCheck(IJml2bConfiguration config, LinkContext f)
		throws Jml2bException {
		tryTk.typeCheck(config, f);
		if (catchTk != null)
			catchTk.typeCheck(config, f);
		if (finallyTk != null)
			finallyTk.typeCheck(config, f);
		return null;
	}

	public Statement jmlNormalize(
		IJml2bConfiguration config,
		Class definingClass)
		throws PogException {
		tryTk = (Statement) tryTk.jmlNormalize(config, definingClass);
		if (catchTk != null)
			catchTk = catchTk.jmlNormalize(config, definingClass);
		if (finallyTk != null)
			finallyTk =
				(Statement) finallyTk.jmlNormalize(config, definingClass);
		return this;
	}

	public StLoops getLoopAtLine(int line) {
		StLoops res = tryTk.getLoopAtLine(line);
		if (res == null && finallyTk != null)
			return finallyTk.getLoopAtLine(line);
		else
			return res;
	}

	static final long serialVersionUID = 1158908701372304229L;

	public void collectCalledMethod(Vector calledMethod) {
		tryTk.collectCalledMethod(calledMethod);
		if (catchTk != null) {
			CatchList tmp = catchTk;
			while (tmp != null) {
				tmp.getBody().collectCalledMethod(calledMethod);
				tmp = tmp.getNext();
			}
		}
		if (finallyTk != null)
			finallyTk.collectCalledMethod(calledMethod);
	}

	public void getAssert(Vector asser) {
		tryTk.getAssert(asser);
		if (catchTk != null) {
			CatchList tmp = catchTk;
			while (tmp != null) {
				tmp.getBody().getAssert(asser);
				tmp = tmp.getNext();
			}
		}
		if (finallyTk != null)
			finallyTk.getAssert(asser);

	}

	public void getSpecBlock(Vector blocks) {
		tryTk.getSpecBlock(blocks);
		if (catchTk != null) {
			CatchList tmp = catchTk;
			while (tmp != null) {
				tmp.getBody().getSpecBlock(blocks);
				tmp = tmp.getNext();
			}
		}
		if (finallyTk != null)
			finallyTk.getSpecBlock(blocks);

	}

	public void getLoop(Vector loops) {
		tryTk.getLoop(loops);
		if (catchTk != null) {
			CatchList tmp = catchTk;
			while (tmp != null) {
				tmp.getBody().getLoop(loops);
				tmp = tmp.getNext();
			}
		}
		if (finallyTk != null)
			finallyTk.getLoop(loops);

	}
}