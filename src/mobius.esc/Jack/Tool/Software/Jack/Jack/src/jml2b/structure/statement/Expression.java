//******************************************************************************
/* Copyright (c) 2002, 2003 GEMPLUS Software Research Labs. All Rights Reserved.
/* Copyright (c) 2003, 2004 INRIA. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: Expression.java
/*
/*******************************************************************************
/* Warnings/Remarks:
/*  09/26/2003 : Simplify integration achieved
/******************************************************************************/
package jml2b.structure.statement;

import jack.util.Logger;

import java.io.ByteArrayInputStream;
import java.io.File;
import java.io.InputStream;
import java.util.Enumeration;
import java.util.Set;
import java.util.Vector;

import jml.ErrorMessage;
import jml.JmlDeclParserTokenTypes;
import jml.JmlLexer;
import jml.JmlParser;
import jml.LineAST;
import jml2b.IJml2bConfiguration;
import jml2b.exceptions.ErrorHandler;
import jml2b.exceptions.InternalError;
import jml2b.exceptions.Jml2bException;
import jml2b.exceptions.LanguageException;
import jml2b.exceptions.LinkException;
import jml2b.exceptions.ParseException;
import jml2b.exceptions.PogException;
import jml2b.formula.BinaryForm;
import jml2b.formula.ElementsForm;
import jml2b.formula.Formula;
import jml2b.formula.IFormToken;
import jml2b.formula.TerminalForm;
import jml2b.link.LinkContext;
import jml2b.link.LinkInfo;
import jml2b.pog.lemma.ExceptionalBehaviourStack;
import jml2b.pog.lemma.FormulaWithSpecMethodDecl;
import jml2b.pog.lemma.LabeledProofsVector;
import jml2b.pog.lemma.Proofs;
import jml2b.pog.substitution.SubArrayElement;
import jml2b.pog.substitution.SubTmpVar;
import jml2b.structure.java.AClass;
import jml2b.structure.java.Class;
import jml2b.structure.java.Field;
import jml2b.structure.java.Identifier;
import jml2b.structure.java.JmlFile;
import jml2b.structure.java.Modifiers;
import jml2b.structure.java.Parameters;
import jml2b.structure.java.ParsedItem;
import jml2b.structure.java.Type;
import jml2b.structure.jml.JmlExpression;
import antlr.collections.AST;

/**
 * This class defines a Java expression.
 **/
public abstract class Expression
	extends Statement
	implements IFormToken, JmlExpression {

	/**
	 * Returns the expression <code>null</code>.
	 * @return the terminal expression <i>LITERAL_null</i>
	 **/
	public static Expression getNull() {
		return new TerminalExp(LITERAL_null, "null");
	}

	/**
	 * Returns the expression <code>false</code>.
	 * @return the terminal expression <i>LITERAL_false</i>
	 **/
	public static Expression getFalse() {
		return new TerminalExp(LITERAL_false, "FALSE");
	}

	/**
	 * Returns the expression <code>true</code>.
	 * @return the terminal expression <i>LITERAL_true</i>
	 **/
	public static Expression getTrue() {
		return new TerminalExp(LITERAL_true, "TRUE");
	}

	/**
	 * Returns the expression <code>0</code>.
	 * @return the terminal expression <i>NUM_INT</i> with <code>nodeText</code> 
	 * 0.
	 **/
	public static Expression getZero() {
		return new TerminalExp(NUM_INT, "0");
	}

	public static Expression getFromString(String expression)
		throws Jml2bException {
		Vector error_vector = new Vector();
		Vector warning_vector = new Vector();

		JmlParser parser = null;

		InputStream stream;

		stream = new ByteArrayInputStream(expression.getBytes());

		try {
			JmlLexer lexer = new JmlLexer(stream);
			lexer.currentFile = new File("");
			parser = new JmlParser(lexer);
			parser.lexer = lexer;
			parser.errorVector = error_vector;
			parser.warningVector = warning_vector;

			parser.currentFile = lexer.currentFile;
			parser.errors = 0;
			parser.warnings = 0;
			parser.JML_reading_JML_file = false; // isJmlFile(f.getName());
			lexer.JML_reading_JML_file = parser.JML_reading_JML_file;
			parser.start_predicate();
			parser.errors += lexer.errors;
		} catch (antlr.RecognitionException e) {
			error_vector.add(new ErrorMessage(e.toString(), -1, -1));
			Logger.err.println("Exception catched : " + e.toString());
		} catch (antlr.TokenStreamException e) {
			error_vector.add(new ErrorMessage(e.toString(), -1, -1));
			Logger.err.println("Exception catched : " + e.toString());
		} catch (NullPointerException e) {
			// catch NullPointerExceptions, since as the parser is initialised in
			// a non classical manner, errors may trigger exceptions.
			error_vector.add(
				new ErrorMessage("Parse Error in Jml parser", -1, -1));
		}

		if (error_vector.size() > 0) {
			// errors have been encountered

			StringBuffer buf = new StringBuffer();
			buf.append("Errors encountered: \n");

			Enumeration e = error_vector.elements();
			while (e.hasMoreElements()) {
				ErrorMessage em = (ErrorMessage) e.nextElement();
				buf.append(em.message);
				buf.append('\n');
			}
			throw new Jml2bException(buf.toString());
		}

		AST tree = parser.getAST();

		Expression result = createE(null, tree);

		result.parse(tree);

		return result;
	}

	/**
	 * Returns the conjonction of two expressions.
	 * @param s1 left part of the conjonction
	 * @param s2 right part of the conjonction
	 * @return <code>s1 && s2</code>
	 **/
	public static BinaryExp and(Expression s1, Expression s2) {
		return new BinaryExp(LOGICAL_OP, s1, "&&", s2);
	}

	/**
	 * Creates an expression from an <code>AST</code> node.
	 * @param jf JML file where is located this expression
	 * @param tree <code>AST</code> node corresponding to this expression
	 * @return the newly created expression to be instanciated by the parse 
	 * methods.
	 * @throws jml2b.exceptions.InternalError when the type of the node does 
	 * not correspond to a known node type.
	 **/
	public static Expression createE(JmlFile jf, AST tree)
		throws Jml2bException {
		switch (tree.getType()) {
			case STAR_ELEMS :
				return new StarElemExp(jf, tree);
			case LCURLY :
				return new ArrayInitializer(jf, tree);
			case QUESTION :
				return new QuestionExp(jf, tree);
			case LITERAL_new :
			case CAST :
			case LITERAL_instanceof :
				return new WithTypeExp(jf, tree);
			case LPAREN :
				return new MethodCallExp(jf, tree);
			case DOT :
			case COMMA :
			case SHIFT_OP :
			case ASSIGN :
			case SHIFT_ASSIGNMENT_OP :
			case BITWISE_ASSIGNMENT_OP :
			case ADDITIVE_ASSIGNMENT_OP :
			case MULTIPLICATIVE_ASSIGNMENT_OP :
			case ADDITIVE_OP :
			case MULTIPLICATIVE_OP :
			case EQUALITY_OP :
			case LOGICAL_OP :
			case BITWISE_OP :
			case RELATIONAL_OP :
			case IMPLICATION_OP :
			case LBRACK :
				return new BinaryExp(jf, tree);
			case QUANTIFIED_EXPR :
				return new QuantifiedExp(jf, tree);
			case T_ELEMTYPE :
			case T_TYPEOF :
			case PRE_INCREMENT_OP :
			case POST_INCREMENT_OP :
			case UNARY_NUMERIC_OP :
			case LNOT :
			case T_OLD :
				//            case T_FRESH :
				return new UnaryExp(jf, tree);
			case NUM_FLOAT :
			case IDENT :
			case CHAR_LITERAL :
			case NUM_INT :
			case LITERAL_false :
			case LITERAL_true :
			case JAVA_BUILTIN_TYPE :
			case LITERAL_null :
			case LITERAL_this :
			case LITERAL_super :
			case STRING_LITERAL :
			case T_RESULT :
				return new TerminalExp(jf, tree);
			case IS_SUBTYPE_OF :
				return new IsSubtypeOfExp(jf, tree);
			case JmlDeclParserTokenTypes.T_TYPE :
				return new TTypeExp(jf, tree);
			case SET :
				if (tree.getFirstChild().getType() == ASSIGN)
					return createE(jf, tree.getFirstChild());
				else
					throw new ParseException(
						jf,
						(LineAST) tree,
						"set can only be used to make an assignment");
			case JmlDeclParserTokenTypes.T_FRESH :
				ErrorHandler.warning(
					jf,
					((LineAST) tree).line,
					((LineAST) tree).column,
					"\\fresh keyword is not handled");
				return new TerminalExp(LITERAL_true, "true");
			case JmlDeclParserTokenTypes.T_NONNULLELEMENTS :
				ErrorHandler.warning(
					jf,
					((LineAST) tree).line,
					((LineAST) tree).column,
					"\\nonnullelements keyword is not handled");
				return new TerminalExp(LITERAL_true, "true");
			default :
				throw new ParseException(jf, (LineAST) tree, "Unknown literal");
		}
	}

	/**
	 * Token defining the expression operator
	 **/
	private int nodeType;

	/**
	 * Text corresponding to the expression operator
	 **/
	private String nodeText;

	/**
	 * Type of the expression
	 **/
	private Type stateType;

	public static final int getPriority(int nodeType) {
			switch (nodeType) {
				case QUANTIFIED_EXPR :
					return 17;
				case T_ELEMTYPE :
				case T_TYPEOF :
					return 18;
				case PRE_INCREMENT_OP :
				case POST_INCREMENT_OP :
					return 16;
				case UNARY_NUMERIC_OP :
					return 16;
				case LNOT :
					return 16;
				case T_OLD :
					return 18;
				case NUM_FLOAT :
				case IDENT :
				case CHAR_LITERAL :
				case NUM_INT :
				case LITERAL_false :
				case LITERAL_true :
				case JAVA_BUILTIN_TYPE :
				case LITERAL_null :
				case LITERAL_this :
				case LITERAL_super :
				case STRING_LITERAL :
				case T_RESULT :
					return 18;
				case IS_SUBTYPE_OF :
					return 12;
				case JmlDeclParserTokenTypes.T_TYPE :
					return 18;
				case SET :
				case JmlDeclParserTokenTypes.T_FRESH :
				case JmlDeclParserTokenTypes.T_NONNULLELEMENTS :
					return 18;
				case QUESTION :
					return 5;
				case LITERAL_new :
					return 16;
				case CAST :
					return 16;
				case LITERAL_instanceof :
					return 12;
				case LPAREN :
				case DOT :
				case LBRACK :
					return 17;
				case IMPLICATION_OP :
				case LOGICAL_OP :
					return 7;
				case COMMA :
					return 18;
				case SHIFT_OP :
					return 13;
				case ADDITIVE_OP :
					return 14;
				case MULTIPLICATIVE_OP :
					return 15;
				case BITWISE_OP :
					return 8;
				case RELATIONAL_OP :
					return 12;
				case BITWISE_ASSIGNMENT_OP :
				case ADDITIVE_ASSIGNMENT_OP :
				case MULTIPLICATIVE_ASSIGNMENT_OP :
				case SHIFT_ASSIGNMENT_OP :
				case ASSIGN :
					return 4;
				case EQUALITY_OP :
					return 11;
					default :
				return 100;
			}
	}

	/**
	 * Constructs an empty expression.
	 **/
	Expression() {
		super();
	}

	/**
	 * Constructs an expression as a <i>parsed item</i>.
	 * @param jf The file where the statement is located
	 * @param tree The <code>AST</code> node corresponding to the statement
	 * @see jml2b.structure.java.ParsedItem#ParsedItem(JmlFile, AST)
	 **/
	Expression(JmlFile jf, AST tree) {
		super(jf, tree);
	}

	/**
	 * Constructs an expression form another one
	 * @param nodeType The node type
	 * @param nodeText The node text
	 **/
	Expression(int nodeType, String nodeText) {
		this.nodeType = nodeType;
		this.nodeText = nodeText;
	}

	/**
	 * Tests if this expression is <i>btrue</i>.
	 * @return <code>true</code> if the expression node type is 
	 * <code>BTRUE</code>, <code>false</code> otherwise
	 **/
	/*@
	  @ requires parsed;
	  @*/
	public final boolean isBTrue() {
		return nodeType == MyToken.BTRUE || nodeType == LITERAL_true;
	}

	/**
	 * Tests if the expression operator is a comma.
	 * @return <code>true</code> if the expression node type is 
	 * <code>COMMA</code>, <code>false</code> otherwise
	 **/
	/*@
	  @ requires parsed;
	  @*/
	public final boolean isComma() {
		return nodeType == COMMA;
	}

	/**
	 * Tests if the expression operator is a dot.
	 * @return <code>true</code> if the expression node type is 
	 * <code>DOT</code>, <code>false</code> otherwise
	 **/
	/*@
	  @ requires parsed;
	  @*/
	public final boolean isDot() {
		return nodeType == DOT;
	}

	/**
	 * Tests if the expression operator is an and.
	 * @return <code>true</code> if the expression node type is 
	 * <code>LOGICAL_OP</code> with node text "&&", <code>false</code> otherwise
	 **/
	/*@
	  @ requires parsed;
	  @*/
	public final boolean isAnd() {
		return nodeType == LOGICAL_OP && nodeText.equals("&&");
	}

	/**
	 * Links the parameters list of a method call and the resulting type to the 
	 * parameters vector.
	 * @param config the current configuration of the generator
	 * @param f The link context
	 * @param parameters The type set of the parameters (constructed here)
	 * @throws Jml2bException
	 **/
	/*@
	  @ requires parsed;
	  @*/
	public void linkParameters(
		IJml2bConfiguration config,
		LinkContext f,
		Vector parameters)
		throws Jml2bException {

		switch (this.nodeType) {
			case COMMA :
				// add the type of the parameter to the parameters vector
				((BinaryExp) this).getLeft().linkParameters(
					config,
					f,
					parameters);
				// add the next parameter
				((BinaryExp) this).getRight().linkParameters(
					config,
					f,
					parameters);
				break;
			default :
				LinkInfo param_type = linkStatement(config, f);
				if (param_type == null) {
					throw new LinkException(
						"Expression.linkParameters: Expected "
							+ "non-null LinkInfo",
						this);
				}
				if (param_type.getType() == null) {
					throw new LinkException(
						"Expression.linkParameters: Expected"
							+ " parameter type in LinkInfo",
						this);
				}
				// add the parsed type to the signature (the parameters vector)
				parameters.add(param_type.getType());
		}
	}

	/**
	 * Links a method call.
	 * @param config the current configuration of the generator
	 * @param f link context
	 * @param parameters set of types of the method parameters
	 * @return the resulting link informations
	 * @throws Jml2bException
	 **/
	/*@
	  @ requires parsed;
	  @*/
	public final LinkInfo linkMethod(
		IJml2bConfiguration config,
		LinkContext f,
		Vector parameters)
		throws Jml2bException {
		switch (nodeType) {
			case DOT :
				LinkInfo tmp =
					((BinaryExp) this).getLeft().linkStatement(config, f);
				LinkContext l = new LinkContext(f, tmp);
				return ((BinaryExp) this).getRight().linkMethod(
					config,
					l,
					parameters);
			case IDENT :
				{
					AClass cl = f.getCurrentClass();
					((TerminalExp) this).getIdent().idType =
						Identifier.ID_METHOD;

					((TerminalExp) this).getIdent().mth =
						cl.lookupMethod(
							config,
							((TerminalExp) this).getIdent().getName(),
							parameters);

					if (((TerminalExp) this).getIdent().mth == null) {

						throw new LinkException(
							"Method not found : "
								+ cl.getName()
								+ "."
								+ ((TerminalExp) this).getIdent().getName()
								+ "("
								+ parameters.toString()
								+ ")",
							this);
					}

					// return a LinkInfo corresponding to the return type of
					// the method
					return new LinkInfo(
						((TerminalExp) this).getIdent().mth.getReturnType());
				}

				// the next two following cases correspond to the use of super
				// and this in order to call constructors. 
				// the other uses of super and this will not be encountered here,
				// since those case correspond to cases where super and this are
				// on the left of a dot.

			case LITERAL_super :
				{
					// look for a constructor in the super class
					// => get super class
					AClass cl = f.getCurrentClass();
					if (cl == null) {
						// should not happen
						throw new LinkException(
							"null class when looking for "
								+ "super constructor",
							this);
					}
					cl = cl.getSuperClass();
					((TerminalExp) this).linkConstructorCall(
						config,
						cl,
						parameters);
					return null;
				}
			case LITERAL_this :
				{
					// look for a constructor in the current class
					((TerminalExp) this).linkConstructorCall(
						config,
						f.getCurrentClass(),
						parameters);
					return null;
				}
			default :
				throw new InternalError(
					"Expression.linkMethod : Don't know how to link "
						+ MyToken.nodeString[nodeType]);

		}
	}

	/**
	 * Normalized comma expression <code>(a,b),c</code> in <code>a,(b,c)</code>.
	 * @param t
	 * @return the normalized expression 
	 **/
	/*@
	  @ requires parsed;
	  @*/
	public final Expression normComma(Expression t) {
		if (nodeType == COMMA) {
			if (t == null)
				return ((BinaryExp) this).getLeft().normComma(
					((BinaryExp) this).getRight());
			Expression s =
				new BinaryExp(COMMA, ((BinaryExp) this).getRight(), ",", t);
			return ((BinaryExp) this).getLeft().normComma(s);
		} else {
			if (t == null)
				return this;
			Expression s = new BinaryExp(COMMA, this, ",", t);
			return s;
		}
	}

	/**
	 * Converts the expression into a formula.
	 * @param config the current configuration of the generator
	 * @return the resulting formula
	 * @throws PogException
	 **/
	/*@
	  @ requires parsed;
	  @*/
	public final FormulaWithSpecMethodDecl exprToForm(IJml2bConfiguration config)
		throws Jml2bException, PogException {
		return exprToForm(config, new Vector(), false);
	}

	/**
	 * Converts the expression, considered as a predicate into a formula
	 * @param config the current configuration of the generator
	 * @return the resulting formula
	 * @throws PogException
	 **/
	/*@
	  @ requires parsed;
	  @*/
	public final FormulaWithSpecMethodDecl predToForm(IJml2bConfiguration config)
		throws Jml2bException, PogException {
		return exprToForm(config, new Vector(), true) /*.exprToBool()*/;
	}

	/**
	 * Converts the expression into a formula.
	 * @param config the current configuration of the generator
	 * @param methods set of the method that have already been analyzed
	 * @return the resulting formula
	 * @throws PogException when this expression contains a method call to a
	 * method that already belongs to the set of analyzed method. That 
	 * corresponds to a loop into pure method call in specification
	 **/
	/*@
	  @ requires parsed;
	  @*/
	final FormulaWithSpecMethodDecl exprToForm(
		IJml2bConfiguration config,
		Vector methods,
		boolean pred)
		throws Jml2bException, PogException {
		return exprToContextForm(config, methods, pred);
	}

	public String emit() {
		return toJava(0) + ";\n";
	}

	/**
	 * Sets the state type value.
	 * @param s state type value
	 **/
	/*@
	  @ requires parsed;
	  @*/
	public final void setStateType(Type s) {
		stateType = s;
	}

	/**
	 * @see Statement#wp(IJml2bConfiguration, Proofs, Proofs, LabeledProofsVector, 
	 * LabeledProofsVector, ExceptionalBehaviourStack)
	 **/
	public final Proofs wp(
		IJml2bConfiguration config,
		Proofs normalBehaviour,
		Proofs finishOnReturn,
		LabeledProofsVector finishOnBreakLab,
		LabeledProofsVector finishOnContinueLab,
		ExceptionalBehaviourStack exceptionalBehaviour)
		throws Jml2bException, PogException {
		return wp(config, fresh(), normalBehaviour, exceptionalBehaviour);
	}

	/**
	 * Return the value associated to a constant expression.
	 * <p>
	 * This method should only be called if isConstant returned true.
	 * @return the integer value of the expression
	 */
	/*@
	  @ requires parsed && isConstant();
	  @*/
	public int getValue() {
		throw new InternalError("getValue() called for non-constant expression");
	}

	/**
	 * Evaluates an element of an array initializer.
	 * @param config the current configuration of the generator
	 * @param field The formula corresponding to the array name
	 * @param fieldType The array elements type
	 * @param length The temporary variable corresponding to the length of the 
	 * array
	 * @param normalBehaviour The theorems to prove when the evaluation
	 * terminates normally
	 * @param exceptionalBehaviour The theorems to prove when the evaluation
	 * terminates abruptly on an exception
	 * @throws PogException
	 **/
	/*@
	  @ requires parsed;
	  @*/
	Proofs arrayDeclaration(
		IJml2bConfiguration config,
		Formula field,
		Type fieldType,
		String length,
		Proofs normalBehaviour,
		ExceptionalBehaviourStack exceptionalBehaviour,
		int indice)
		throws Jml2bException, PogException, LanguageException {
		String vv = fresh();
		String elements =
			ElementsForm
				.getElementsName(fieldType.getElemType())
				.getNonAmbiguousName();
		BinaryForm newElements;
		if (indice == 0)
			newElements =
				new BinaryForm(
					B_OVERRIDING,
					ElementsForm.getElementsName(fieldType.getElemType()),
					new BinaryForm(
						B_COUPLE,
						field,
						new BinaryForm(
							B_COUPLE,
							new TerminalForm(indice),
							new TerminalForm(vv))));
		// newElements = elements 
		//               <+ {field |-> {indice |-> vv}}
		else
			newElements =
				new BinaryForm(
					B_OVERRIDING,
					ElementsForm.getElementsName(fieldType.getElemType()),
					new BinaryForm(
						B_COUPLE,
						field,
						new BinaryForm(
							B_OVERRIDING,
							new BinaryForm(
								IFormToken.B_APPLICATION,
								ElementsForm.getElementsName(
									fieldType.getElemType()),
								field),
							new BinaryForm(
								B_COUPLE,
								new TerminalForm(indice),
								new TerminalForm(vv)))));
		// newElements = elements 
		//               <+ {field |-> elements(field) <+ {indice |-> vv}}

		Proofs t =
			wp(
				config,
				vv,
				normalBehaviour.sub(new SubArrayElement(elements, newElements)),
				exceptionalBehaviour);
		return t.sub(new SubTmpVar(length, new TerminalForm(indice + 1)));
	}

	/**
	 * Renames the fields belonging to the parameter list with new names.
	 * @param signature the signature of the called method
	 * @param newSignature the list of new names
	 * @return the current formula renamed
	 * @see jml2b.pog.Proofs#renameParam(Parameters, Vector)
	 **/
	public Expression renameParam(
		Parameters signature,
		Parameters newSignature) {
		return renameParam(
			signature.signature.elements(),
			newSignature.signature.elements());
	}

	/**
	 * Renames the fields belonging to the parameter list with new names.
	 * @param signature the signature of the called method
	 * @param newSignature the list of new names
	 * @return the current formula renamed
	 * @see jml2b.pog.Proofs#renameParam(Parameters, Vector)
	 **/
	private Expression renameParam(
		Enumeration signature,
		Enumeration newSignature) {
		if (signature.hasMoreElements()) {
			Field f = (Field) signature.nextElement();
			Field newF = (Field) newSignature.nextElement();
			return renameParam(signature, newSignature).subField(f, newF);
		} else
			return (Expression) clone();
	}

	public abstract Expression subField(Field f, Field newF);

	public abstract Expression subResult(String ww) ;
	
	/**
	 * Collects all the indentifier of the statement to give them an index in 
	 * the identifer array. This array is then analyzed to give short name when 
	 * it is possible to identifiers.
	 * @see jml2b.pog.IdentifierResolver#bIdents
	 **/
	/*@
	  @ requires parsed;
	  @*/
	public abstract void processIdent();

	/*@
	  @ requires parsed;
	  @*/
	public final Statement jmlNormalize(
		IJml2bConfiguration config,
		Class definingClass) {
		processIdent();
		return (Expression) instancie();
	}

	/**
	 * Returns whether two expressions are equal.
	 * @param e The tested expression
	 * @return <code>true</code> if the expression equals the parameter, 
	 * <code>false</code> otherwise
	 **/
	/*@
	  @ requires parsed && e != null;
	  @*/
	public abstract boolean equals(Expression e);

	/** 
	 * Replaces <code>this</code> with the parameter in the expression.
	 * @param b expression on which the method where the expression occurs is 
	 * called.
	 * @return the modified expression
	 **/
	/*@
	  @ requires parsed;
	  @*/
	public abstract JmlExpression instancie(Expression b);

	/**
	 * Returns whether this expression is a constant.
	 * @return <code>true</code> if the expression is a constant, 
	 * <code>false</code> otherwise
	 **/
	/*@
	  @ requires parsed;
	  @*/
	public abstract /*@ pure */
	boolean isConstant();

	/**
	 * Converts <i>old</i> pragma in <i>called old</i> pragma.
	 **/
	/*@
	  @ requires parsed;
	  @*/
	public abstract void old();

	//	abstract Vector getFreshVars();

	/**
	 * Displays the expression corresponding to a part of a method specification
	 * in a tool tip with the initial Java syntax.
	 * @return the string corresponding to this expression
	 **/
	public abstract String toJava(int indent);

	/**
	 * Converts the expression in a formula with a context issue from the pure
	 * method call.
	 * @param config the current configuration of the generator
	 * @param methods The set of methods that have already been analyzed
	 * @return the resulting formula with a context
	 * @throws PogException when this expression contains a method call to a
	 * method that already belongs to the set of analyzed method. That 
	 * corresponds to a loop into pure method call in specification
	 **/
	/*@
	  @ requires parsed 
	  @       && methods != null 
	  @       && methods.elementType <: \type(Method);
	  @*/
	abstract FormulaWithSpecMethodDecl exprToContextForm(
		IJml2bConfiguration config,
		Vector methods,
		boolean pred)
		throws Jml2bException, PogException;

	/**
	 * Returns the proofs resulting where the WP calculus apply on this 
	 * expression. The calculus is only applied on Java expression.
	 * @param config the current configuration of the generator
	 * @param resultingVar temporary variable corresponding to the
	 * expression evaluation
	 * @param normalBehaviour theorems to ensure if the expression evaluation 
	 * terminates normally
	 * @param exceptionalBehaviour exceptional theorems to ensure if the
	 * expression evaluation terminates abruply on an exception
	 * @return the proofs obligation resulting from the WP calculus
	 * @throws PogException
	 **/
	/*@
	  @ requires parsed;
	  @*/
	public abstract Proofs wp(
		IJml2bConfiguration config,
		String result,
		Proofs normalBehaviour,
		ExceptionalBehaviourStack exceptionalBehaviour)
		throws Jml2bException, PogException;

	/**
	 * Tests whether the expression contains fields that have modifiers 
	 * compatible with the invariant modifiers.
	 * <UL>
	 * <li> If the invariant is static, all fields should be static.
	 * <li> If the invariant is private, all fields should be private.
	 * <li> If the invariant is package-visible, all fields should be almost 
	 * package-visible.
	 * <li> If the invariant is protected, all fields should be almost protected.
	 * </UL>
	 * @param config TODO
	 * @param modifiers The current invariant modifiers
	 * @throws LinkException when the test fails.
	 **/
	/*@
	  @ requires parsed;
	  @*/
	public abstract void isModifiersCompatible(IJml2bConfiguration config, Modifiers modifiers)
		throws LinkException;

	/**
	 * Returns the set of parsed items that correspond to this expression
	 * @return the set of parsed item that correspond to the complete 
	 * expression 
	 **/
	/*@
	  @ requires parsed;
	  @*/
	public abstract Vector getParsedItems();

	public abstract void setParsedItem(ParsedItem pi);

	/**
	 * Returns the stateType.
	 * @return Type
	 */
	/*@
	  @ requires parsed;
	  @*/
	public final Type getStateType() {
		return stateType;
	}

	/**
	 * Returns the nodeText.
	 * @return String
	 */
	/*@
	  @ requires parsed;
	  @*/
	public final String getNodeText() {
		return nodeText;
	}

	/**
	 * Sets the nodeText.
	 * @param nodeText The nodeText to set
	 */
	/*@
	  @ requires parsed;
	  @*/
	public final void setNodeText(String nodeText) {
		this.nodeText = nodeText;
	}

	/**
	 * Returns the nodeType.
	 * @return int
	 */
	/*@
	  @ requires parsed;
	  @*/
	public final int getNodeType() {
		return nodeType;
	}

	/**
	 * Sets the nodeType.
	 * @param nodeType The nodeType to set
	 */
	/*@
	  @ requires parsed;
	  @*/
	public final void setNodeType(int nodeType) {
		this.nodeType = nodeType;
	}

	static final long serialVersionUID = -5713906842836394348L;

	/**
	 * @param indent
	 * @return
	 */
	static String indent(int indent) {
		String res = "";
		for (int i = 0; i < indent; i++)
			res += " ";
		return res;
	}

	abstract void getFreeVariable(Set s);

	public Expression addInConjonction(Expression req) {
		if (req.getNodeType() == LOGICAL_OP
			&& req.getNodeText().equals("&&")) {
			Expression tmp = addInConjonction(((BinaryExp) req).getLeft());
			return tmp.addInConjonction(((BinaryExp) req).getRight());
		} else if (!containsConjonctionAtom(req)) {
			return new BinaryExp(LOGICAL_OP, this, "&&", req);
		} else
			return this;
	}

	boolean containsConjonctionAtom(Expression req) {
		if (getNodeType() == LOGICAL_OP && getNodeText().equals("&&")) {
			return ((BinaryExp) this).getLeft().containsConjonctionAtom(req)
				|| ((BinaryExp) this).getRight().containsConjonctionAtom(req);

		} else
			return equals(req);
	}

	public void getAssert(Vector asser) {
	}

	public void getSpecBlock(Vector blocks) {
	}

	public void getLoop(Vector blocks) {
	}


}
