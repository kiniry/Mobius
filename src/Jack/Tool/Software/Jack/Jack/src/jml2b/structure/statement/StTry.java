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
import jml2b.pog.lemma.ExceptionalBehaviourStack;
import jml2b.pog.lemma.ExceptionalProofs;
import jml2b.pog.lemma.LabeledProofsVector;
import jml2b.pog.lemma.Proofs;
import jml2b.pog.util.ColoredInfo;
import jml2b.pog.util.IdentifierResolver;
import jml2b.structure.java.Class;
import jml2b.structure.java.Field;
import jml2b.structure.java.JmlFile;
import jml2b.structure.java.ParsedItem;
import jml2b.structure.java.Type;
import jml2b.util.ModifiableSet;
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

	String emit() {
		String s =
			"catch ("
				+ catchParam.getType().toJava()
				+ " "
				+ catchParam.getName()
				+ ") {\n"
				+ body.emit()
				+ "}\n";
		if (next != null)
			s += next.emit();
		return s;
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

	/**
	 * Calculates the stack of exceptional proofs resulting from the application
	 * of each catch clause of the list on the current proof context.
	 * @param config The current configuration
	 * @param normalBehaviour theorems to ensure if the statement terminates
	 * normally
	 * @param finishOnReturn theorems to ensure if the statement terminates
	 * abruptly on a <code>return</code>
	 * @param finishOnBreakLab labelled theorems to ensure if the statement
	 * terminates abruptly on a <code>break</code>
	 * @param finishOnContinueLab labelled theorems to ensure if the statement
	 * terminates abruptly on a <code>continue</code>
	 * @param exceptionalBehaviour exceptional theorems to ensure if the
	 * statement terminates abruply on an exception
	 * @return the proofs obligation resulting from the WP calculus
	 * @throws PogException
	 **/
	/*@
	  @ requires parsed;
	  @*/
	ExceptionalBehaviourStack newExceptionalBehaviour(
		IJml2bConfiguration config,
		Proofs normalBehaviour,
		Proofs finishOnReturn,
		LabeledProofsVector finishOnBreakLab,
		LabeledProofsVector finishOnContinueLab,
		ExceptionalBehaviourStack exceptionalBehaviour)
		throws Jml2bException, PogException {
		// the exceptional proof corresponding to the body of the catch clause
		// applied on the proof context.
		ExceptionalProofs ep =
			new ExceptionalProofs(
				catchParam.getType(),
				catchParam,
				(
					(Proofs) body
						.wp(
							config,
							normalBehaviour,
							finishOnReturn,
							finishOnBreakLab,
							finishOnContinueLab,
							exceptionalBehaviour)
						.clone())
						.addBox(
					new ColoredInfo(this)));

		if (next != null)
			return next
				.newExceptionalBehaviour(
					config,
					normalBehaviour,
					finishOnReturn,
					finishOnBreakLab,
					finishOnContinueLab,
					exceptionalBehaviour)
				.push(ep);
		else
			return new ExceptionalBehaviourStack(ep);
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

	public String emit() {
		String s = "try  {\n" + tryTk.emit() + "}\n";
		if (catchTk != null)
			s += catchTk.emit();
		if (finallyTk != null)
			s += "finally {\n" + finallyTk.emit() + "}\n";
		return s;
	}

	/**
	* Constructs a try catch finally statement from another one.
	* @param tryTk The try statement
	* @param catchTk The catch statement list
	* @param finallyTk The finally statement
	**/
	/*@
	  @ requires tryTk != null 
	  @       && (catchTk != null ==> catchTk.parsed)
	  @       && (finallyTk ! =null ==> finallyTk.parsed);
	  @*/
	private StTry(Statement tryTk, CatchList catchTk, Statement finallyTk) {
		super();
		this.tryTk = tryTk;
		this.catchTk = catchTk;
		this.finallyTk = finallyTk;
		//@ set parsed = true;
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

	public Proofs wp(
		IJml2bConfiguration config,
		Proofs normalBehaviour,
		Proofs finishOnReturn,
		LabeledProofsVector finishOnBreakLab,
		LabeledProofsVector finishOnContinueLab,
		ExceptionalBehaviourStack exceptionalBehaviour)
		throws Jml2bException, PogException {
		Proofs res;
		if (catchTk == null) {
			// catch == null and finally != null
			// Applies the finally statement to each termination case proofs.
			// Normal behaviour
			Proofs st1 =
				finallyTk.wp(
					config,
					normalBehaviour,
					finishOnReturn,
					finishOnBreakLab,
					finishOnContinueLab,
					exceptionalBehaviour);
			// finish on return proof as the normal behaviour
			Proofs st2 =
				finallyTk.wp(
					config,
					finishOnReturn,
					finishOnReturn,
					finishOnBreakLab,
					finishOnContinueLab,
					exceptionalBehaviour);
			// finish on break proof as the normal behaviour        
			LabeledProofsVector st3 =
				finishOnBreakLab.finallyLab(
					config,
					finallyTk,
					finishOnReturn,
					finishOnBreakLab,
					finishOnContinueLab,
					exceptionalBehaviour);
			// finish on continue proof as the normal behaviour        
			LabeledProofsVector st4 =
				finishOnContinueLab.finallyLab(
					config,
					finallyTk,
					finishOnReturn,
					finishOnBreakLab,
					finishOnContinueLab,
					exceptionalBehaviour);
			// exceptional behaviour proof as the normal behaviour        
			ExceptionalBehaviourStack st5 =
				exceptionalBehaviour.finallyOnExceptionalBehaviour(
					config,
					finallyTk,
					finishOnReturn,
					finishOnBreakLab,
					finishOnContinueLab,
					exceptionalBehaviour);
			// Applies the try statement on the resulting proofs.
			res = tryTk.wp(config, st1, st2, st3, st4, st5);
		} else if (finallyTk == null) {
			// catch != null finally == null
			// Calculates the proof resulting for the application of the catch
			// clauses on the normal behaviour.
			ExceptionalBehaviourStack newEx =
				catchTk.newExceptionalBehaviour(
					config,
					normalBehaviour,
					finishOnReturn,
					finishOnBreakLab,
					finishOnContinueLab,
					exceptionalBehaviour);

			// Adds the proofs to the exceptional behaviour exceptional proofs
			// stack.        
			int size = exceptionalBehaviour.size();
			exceptionalBehaviour = exceptionalBehaviour.addAll(newEx);
			// Applies the try statement on the resulting proofs.
			res =
				tryTk.wp(
					config,
					normalBehaviour,
					finishOnReturn,
					finishOnBreakLab,
					finishOnContinueLab,
					exceptionalBehaviour);

			// Restore the exceptional behaviour exceptional proofs stack.      
			exceptionalBehaviour = exceptionalBehaviour.pop(size);
		} else {
			// catch != null finally != null
			// Transforms the try{t} catch{c} finally{f} into 
			// try{try{t} catch{c}} finally{f} statement.
			res =
				new StTry(new StTry(tryTk, catchTk, null), null, finallyTk).wp(
					config,
					normalBehaviour,
					finishOnReturn,
					finishOnBreakLab,
					finishOnContinueLab,
					exceptionalBehaviour);
		}
		res.gc(config, true);
		return res;
	}

	public StLoops getLoopAtLine(int line) {
		StLoops res = tryTk.getLoopAtLine(line);
		if (res == null && finallyTk != null)
			return finallyTk.getLoopAtLine(line);
		else
			return res;
	}

	static final long serialVersionUID = 1158908701372304229L;

	public void getPrecondition(
		IJml2bConfiguration config,
		ModifiableSet modifies,
		Vector req,
		Vector ens)
		throws Jml2bException, PogException {
		tryTk.getPrecondition(config, modifies, req, ens);
		if (catchTk != null) {
			CatchList tmp = catchTk;
			while (tmp != null) {
				tmp.getBody().getPrecondition(config, modifies, req, ens);
				tmp = tmp.getNext();
			}
		}
	}
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