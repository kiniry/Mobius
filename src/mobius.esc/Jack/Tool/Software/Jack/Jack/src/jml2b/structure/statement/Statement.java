//******************************************************************************
/* Copyright (c) 2002, 2003 GEMPLUS Software Research Labs. All Rights Reserved.
/* Copyright (c) 2003, 2004 INRIA. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: Statement.java
/*
/*******************************************************************************
/* Warnings/Remarks:
/*  09/26/2003 : Simplify integration achieved
/******************************************************************************/
package jml2b.structure.statement;

import java.util.Vector;

import jml.JmlDeclParserTokenTypes;
import jml.LineAST;
import jml2b.exceptions.ErrorHandler;
import jml2b.exceptions.Jml2bException;
import jml2b.exceptions.PogException;
import jml2b.formula.IFormToken;
import jml2b.link.LinkContext;
import jml2b.link.LinkInfo;
import jml2b.link.Linkable;
import jml2b.link.TypeCheckable;
import jml2b.pog.lemma.ExceptionalBehaviourStack;
import jml2b.pog.lemma.LabeledProofsVector;
import jml2b.pog.lemma.Proofs;
import jml2b.pog.lemma.Theorem;
import jml2b.structure.java.AClass;
import jml2b.structure.java.Class;
import jml2b.structure.java.ParsedItem;
import jml2b.util.ModifiableSet;
import antlr.collections.AST;
import jml2b.structure.java.*;
import jml2b.*;

/**
 * This class defines a Java statement.
 * A statement is either:
 * <UL>
 * <li> an expression
 * <li> an assertion
 * <li> a block
 * <li> a control flow break (<code>return</code>, <code>break</code>, 
 * <code>continue</code> or <code>throw</code>)
 * <li> an if
 * <li> an implements label
 * <li> a label
 * <li> a loop (<code>do while</code>, <code>while do</code> or <code>for</code>)
 * <li> a sequence
 * <li> a skip
 * <li> a specified block
 * <li> a switch
 * <li> a try catch finally
 * <li> a variable declaration.
 * </UL>
 * @author L. Burdy
 **/
public abstract class Statement
	extends ParsedItem
	implements JmlDeclParserTokenTypes, MyToken, Linkable, IFormToken, TypeCheckable {

	/**
	 * The {@link jml2b.structure.java.Class} <code>NullPointerException</code>
	 * @see jml2b.pog.Pog#pog(JmlFile, IJml2bConfiguration)
	 **/
	public static AClass nullPointerException = null;

	/**
	 * The {@link jml2b.structure.java.Class} 
	 * <code>ArrayIndexOutOfBoundsException</code>
	 * @see jml2b.pog.Pog#pog(JmlFile, IJml2bConfiguration)
	 **/
	public static AClass arrayIndexOutOfBoundsException = null;

	/**
	 * The {@link jml2b.structure.java.Class} <code>ArithmeticException</code>
	 * @see jml2b.pog.Pog#pog(JmlFile, IJml2bConfiguration)
	 **/
	public static AClass arithmeticException = null;

	/**
	 * The {@link jml2b.structure.java.Class} 
	 * <code>NegativeArraySizeException</code>
	 * @see jml2b.pog.Pog#pog(JmlFile, IJml2bConfiguration)
	 **/
	public static AClass negativeArraySizeException = null;

	/**
	 * The {@link jml2b.structure.java.Class} <code>ClassCastException</code>
	 * @see jml2b.pog.Pog#pog(JmlFile, IJml2bConfiguration)
	 **/
	public static AClass classCastException = null;

	/**
	 * The {@link jml2b.structure.java.Class} <code>ArrayStoreException</code>
	 * @see jml2b.pog.Pog#pog(JmlFile, IJml2bConfiguration)
	 **/
	public static AClass arrayStoreException = null;

	/**
	 * Counter allowing to create fresh temporary variable.
	 **/
	private static int fresh = 0;

	/**
	 * Returns a fresh temporary variable.
	 * @return a tempory variable "T<i>xxx</i>"
	 **/
	public static String fresh() {
		return "T" + fresh++;
	}

	/**
	 * Counter allowing to create fresh <i>new object</i> variable.
	 **/
	private static int freshObject = 0;

	/**
	 * Returns a fresh <i>new object</i> variable.
	 * @return a <i>new object</i> variable "newObject_<i>xxx</i>"
	 **/
	public static String freshObject() {
		return "newObject_" + freshObject++;
	}

	/**
	 * Counter allowing to create fresh <i>returned from method call</i> 
	 * variable.
	 **/
	private static int freshResult = 0;

	/**
	 * Returns a fresh <i>returned from method call</i> variable.
	 * @return a <i>returned from method call</i> variable 
	 * "Result_<i>xxx</i>"
	 **/
	public static String freshResult(String m) {
		return "Result_" + m + "_" + freshResult++;
	}
	
	private static int freshMethod = 0;
	public static String freshMethod(String m) {
		return "Def_" + m + "_" + freshMethod++;
	}

	/**
	 * Counter allowing to create fresh <code>refelements</code> variable.
	 **/
	private static int freshRefelements = 0;

	/**
	 * Returns a fresh <i>refelements</i> variable.
	 * @return a <i>refelements</i> variable 
	 * "refelements<i>xxx</i>"
	 **/
	static String freshRefelements() {
		return "refelements" + freshRefelements++;
	}

	/**
	 * Initialize global variables for name generation.
	 **/
	public static void initFresh() {
		fresh = 0;
		freshObject = 0;
		freshResult = 0;
		freshRefelements = 0;
	}

	/*@
	  @ protected ghost boolean parsed = false;
	  @*/

	/**
	 * Constructs a statement by default.
	 **/
	Statement() {
		super();
	}

	/**
	 * Constructs a statement as a <i>parsed item</i>.
	 * @param jf The file where the statement is located
	 * @param tree The <code>AST</code> node corresponding to the statement
	 * @see jml2b.structure.java.ParsedItem#ParsedItem(JmlFile, AST)
	 **/
	Statement(JmlFile jf, AST tree) {
		super(jf, tree);
	}

	/**
	 * Constructs a statement as a <i>parsed item</i> from a <i>parsed item</i>.
	 * @param pi the parsed item corresponding to this statement
	 * @see jml2b.structure.java.ParsedItem#ParsedItem(ParsedItem)
	 **/
	Statement(ParsedItem pi) {
		super(pi);
	}

	/**
	 * Creates a statement from an <code>AST</code>.
	 * @param jf JML file where is located this statement
	 * @param tree <code>AST</code> node corresponding to this statement
	 * @return tne newly created statement to be instanciated by the parse 
	 * methods.
	 **/
	public static Statement createS(JmlFile jf, AST tree)
		throws Jml2bException {
		switch (tree.getType()) {
			case SEMI :
				return new StSkip(jf, tree);
			case LCURLY :
				return new StBlock(jf, tree);
			case COLON :
				return new StLabel(jf, tree);
			case LITERAL_switch :
				return new StSwitch(jf, tree);
			case LITERAL_for :
				return new StFor(jf, tree);
			case LITERAL_do :
			case LITERAL_while :
				return new StDoWhile(jf, tree);
			case LITERAL_if :
				return new StIf(jf, tree);
			case LITERAL_try :
				return new StTry(jf, tree);
			case LITERAL_final :
			case VAR_DECL :
			case GHOST :
				return new StVarDecl(jf, tree);	
			case LITERAL_continue :
			case LITERAL_break :
			case LITERAL_return :
			case LITERAL_throw :
				return new StControlFlowBreak(jf, tree);
			case AFFIRM_KEYWORD :
				return new StAssert(jf, tree);
			case SPEC_STATEMENT :
				return new StSpecBlock(jf, tree);
			case LABEL_KEYWORD :
				return new StImplementsLabel(jf, tree);
			case JmlDeclParserTokenTypes.UNREACHABLE :
				return new StAssert(new TerminalExp(LITERAL_false, "false"));
			case ASSUME_KEYWORD :
				ErrorHandler.warning(
					jf,
					((LineAST) tree).line,
					((LineAST) tree).column,
					"assume keyword is not handled");
				return new StSkip();
			default :
				return Expression.createE(jf, tree);
		}
	}

	/*@
	  @ requires parsed;
	  @*/
	public Object clone() {
		return this;
	}

	/** 
	  * Returns the proofs resulting where the WP calculus apply on this 
	  * statement.
	  * The statement corresponds to a method body.
	  * @param phi1 The normal behaviour to prove if the statement terminates
	  * normally or abruptly on a <code>return</code>.
	  * @param phi7 The exceptional behaviour to prove if the statement 
	  * terminates abruply on an exception.
	  * @param signature The signature of the method.
	  * @return the proof obligations.
	  * @exception PogException if an error occurs during the PO generation.
	  */
	/*@
	  @ requires parsed;
	  @*/
	public final Proofs ensures(
		IJml2bConfiguration config,
		Theorem phi1,
		ExceptionalBehaviourStack phi7,
		Vector signature)
		throws Jml2bException, PogException {

		// Add an old pragma around the parameters.
		phi1.oldParam(signature);

		// Apply the WP calculus : 
		// [this](phi1, phi1, empty vector, empty vector, phi7)
		return wp(
			config,
			new Proofs(phi1),
			(Proofs) (new Proofs(phi1)).clone(),
			new LabeledProofsVector(),
			new LabeledProofsVector(),
			phi7);
	}

	public final Proofs ensures(
		IJml2bConfiguration config,
		Proofs phi1,
		ExceptionalBehaviourStack phi7)
		throws Jml2bException, PogException {

		// Apply the WP calculus : 
		// [this](phi1, phi1, empty vector, empty vector, phi7)
		return wp(
			config,
			phi1,
			(Proofs) phi1.clone(),
			new LabeledProofsVector(),
			new LabeledProofsVector(),
			phi7);
	}
	/**
	 * @see jml2b.link.Linkable#link(IJml2bConfiguration, LinkContext)
	 **/
	/*@
	  @ requires parsed;
	  @*/
	public final void link(IJml2bConfiguration config, LinkContext f)
		throws Jml2bException {
		// nothing
		// linkStatement(f);
	}

	/**
	 * @see jml2b.link.Linkable#linkStatements(IJml2bConfiguration, LinkContext)
	 **/
	/*@
	  @ requires parsed;
	  @*/
	public final int linkStatements(IJml2bConfiguration config, LinkContext f)
		throws Jml2bException {
		linkStatement(config, f);
		return 0;
	}

	/**
	 * Returns the first statement in a sequence.
	 * If the statement is not a sequence, return it.
	 * @return <code>this</code>
	 * @see StSequence#firstStatement()
	 **/
	/*@
	  @ requires parsed;
	  @*/
	public Statement firstStatement() {
		return this;
	}

	/**
	 * Returns the tail statement in a sequence considered as a list.
	 * If the statement is not a sequence, return it.
	 * @return <code>this</code>
	 * @see StSequence#tail()
	 **/
	/*@
	  @ requires parsed;
	  @*/
	public Statement tail() {
		return null;
	}

	/**
	 * Parses an <code>AST</code> tree in order to instanciate the statement 
	 * fields.
	 * @param tree <code>AST</code> tree containing the statement
	 * @throws Jml2bException when a parse error occurs.
	 **/
	/*@
	  @ modifies parsed;
	  @ ensures parsed;
	  @*/
	public abstract AST parse(AST tree) throws Jml2bException;

	/**
	 * Links the statement.
	 * @return the link info resulting from the link
	 * @throws Jml2bException
	 **/
	/*@
	  @ requires parsed;
	  @*/
	public abstract LinkInfo linkStatement(
		IJml2bConfiguration config,
		LinkContext f)
		throws Jml2bException;

	/**
	 * Collects all the indentifier of the statement to give them an index in 
	 * the identifer array. This array is then analyzed to give short name when 
	 * it is possible to identifiers.
	 * Instancie the statement.
	 * More <a href="{@docRoot}/jml2b/structure/java/doc-files/instancie.html"> 
	 * informations</a> on instancie.
	 * @param definingClass The class where this statement is defined
	 * @return the normalized statement
	 * @see jml2b.pog.IdentifierResolver#bIdents
	 **/
	/*@
	  @ requires parsed;
	  @*/
	public abstract Statement jmlNormalize(
		IJml2bConfiguration config,
		Class definingClass)
		throws PogException;

	/**
	 * Returns the proofs resulting where the WP calculus apply on this 
	 * statement.
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
	public abstract Proofs wp(
		IJml2bConfiguration config,
		Proofs normalBehaviour,
		Proofs finishOnReturn,
		LabeledProofsVector finishOnBreakLab,
		LabeledProofsVector finishOnContinueLab,
		ExceptionalBehaviourStack exceptionalBehaviour)
		throws Jml2bException, PogException;

	public abstract String emit();

	static final long serialVersionUID = -5713906842836394348L;

	/**
	 * @param line
	 * @return
	 */
	public StLoops getLoopAtLine(int line) {
		return null;
	}

	public abstract void getPrecondition(
		IJml2bConfiguration config,
		ModifiableSet modifies,
		Vector req,
		Vector ens)
		throws Jml2bException, PogException;

	public abstract void collectCalledMethod(Vector calledMethod);

	public abstract void getAssert(Vector asser);

	public abstract void getSpecBlock(Vector blocks);

	public abstract void getLoop(Vector loops);

}
