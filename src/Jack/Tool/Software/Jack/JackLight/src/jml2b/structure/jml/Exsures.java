//******************************************************************************
/* Copyright (c) 2002, 2003 GEMPLUS Software Research Labs. All Rights Reserved.
/* Copyright (c) 2003, 2004 INRIA. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: Exsures.java
/*
/*******************************************************************************
/* Warnings/Remarks:
/******************************************************************************/
package jml2b.structure.jml;

import jack.util.Logger;

import java.io.ByteArrayInputStream;
import java.io.File;
import java.io.InputStream;
import java.io.Serializable;
import java.util.Enumeration;
import java.util.Vector;

import jml.ErrorMessage;
import jml.JmlDeclParserTokenTypes;
import jml.JmlLexer;
import jml.JmlParser;
import jml.LineAST;
import jml2b.IJml2bConfiguration;
import jml2b.exceptions.Jml2bException;
import jml2b.exceptions.TokenException;
import jml2b.exceptions.TypeCheckException;
import jml2b.link.LinkContext;
import jml2b.link.Linkable;
import jml2b.link.TypeCheckable;
import jml2b.pog.util.IdentifierResolver;
import jml2b.structure.java.Field;
import jml2b.structure.java.JmlFile;
import jml2b.structure.java.Parameters;
import jml2b.structure.java.ParsedItem;
import jml2b.structure.java.Type;
import jml2b.structure.statement.Expression;
import jml2b.structure.statement.QuantifiedExp;
import jml2b.structure.statement.QuantifiedVar;
import jml2b.util.Profiler;
import antlr.collections.AST;

/**
 * This class implements an <i>exsures</i> clause, that is an exception type, a 
 * field corresponding to the exception and a property.
 * @author L. Burdy
 * @author A. Requet
 **/
public class Exsures
	extends Profiler
	implements Linkable, TypeCheckable, Serializable {

	/**
	 * Stores the exsures clauses corresponding to <code>str</code> into
	 * <code>v</code>.
	 * @param str the string that should be parsed.
	 * @param v the vector where the resulting exsures are stored.
	 * @throws Jml2bException
	 */
	/*@ requires str != null;
	  @ requires v != null;
	  @*/
	public static void getExsures(String str, Vector v) throws Jml2bException {
		Vector error_vector = new Vector();
		Vector warning_vector = new Vector();

		JmlParser parser = null;

		InputStream stream;

		stream = new ByteArrayInputStream(("exsures " + str + ";").getBytes());
		try {
			JmlLexer lexer = new JmlLexer(stream);
			// added a dummy file in order to prevent NullPointerExceptions
			// when printing messages
			lexer.currentFile = new File("Exsures");
			parser = new JmlParser(lexer);
			parser.lexer = lexer;
			parser.errorVector = error_vector;
			parser.warningVector = warning_vector;

			parser.currentFile = lexer.currentFile;
			parser.errors = 0;
			parser.warnings = 0;
			parser.JML_reading_JML_file = true; // isJmlFile(f.getName());
			lexer.JML_reading_JML_file = parser.JML_reading_JML_file;
			parser.start_signals();
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

		parseExsures(null, tree, -1, v);
	}

	/**
	 * Parses an exsures clause
	 * @param jmlFile The currently parsed JML file
	 * @param a The parsed AST tree
	 * @param first_line The current estimated first line of the method
	 * @param dest The constructed set of Exsures clause
	 * @return The updated estimated first line of the method
	 * @throws Jml2bException
	 */
	static int parseExsures(
		JmlFile jmlFile,
		AST a,
		int first_line,
		Vector dest)
		throws Jml2bException {
		while (a != null) {
			if (a.getType() != JmlDeclParserTokenTypes.SIGNALS_KEYWORD) {
				throw new TokenException(
					jmlFile,
					(LineAST) a,
					"Method.parseExsures",
					"SIGNALS_KEYWORD",
					a.getType());
			}
			if (((LineAST) a).line < first_line)
				first_line = ((LineAST) a).line;

			AST current = a.getFirstChild();
			if (current.getType() != JmlDeclParserTokenTypes.LPAREN) {
				throw new TokenException(
					jmlFile,
					(LineAST) a,
					"Method.parseExsures",
					"LPAREN",
					current.getType());
			}
			current = current.getNextSibling();
			// parse the type of the exception
			Type ex_type = new Type(jmlFile, current);
			ex_type.parse(current);
			current = current.getNextSibling();

			String ex_name = null;
			if (current.getType() == JmlDeclParserTokenTypes.IDENT) {
				ex_name = current.getText();
				current = current.getNextSibling();
			}
			if (current.getType() != JmlDeclParserTokenTypes.RPAREN) {
				throw new TokenException(
					jmlFile,
					(LineAST) a,
					"Method.parseExsures",
					"RPAREN",
					current.getType());
			}
			current = current.getNextSibling();
			Expression ex_statement = Expression.createE(jmlFile, current);
			ex_statement.parse(current);

			Exsures exs = new Exsures(ex_type, ex_name, ex_statement);

			dest.add(exs);

			// next exsures clause
			a = a.getNextSibling();
		}

		return first_line;
	}

	/**
	 * The type of the exception.
	 */
	private Type exceptionType;

	/** 
	 * The field corresponding to the catched exception.
	 */
	private Field exceptionField;

	/**
	 * The property ensured by this <i>exsures</i> clause.
	 **/
	private Expression expression;

	/*@
	  @ invariant expression != null;
	  @ invariant exceptionType != null;
	  @*/

	/**
	 * Constructs an exsures clause from a cloned one.
	 * @param t The type of the exception.
	 * @param f The field corresponding to the catched exception.
	 * @param s The ensured property
	 **/
	/*@
	  @ requires s != null;
	  @ requires t != null;
	  @*/
	private Exsures(Type t, Field f, Expression s) {
		exceptionType = t;
		exceptionField = f;
		expression = s;
	}

	/** 
	 * Constructs an exsure clause.
	 * @param t The type of the exception
	 * @param name The name of the thrown exception in the property. It can be 
	 * <code>null</code>,  meaning that the exception is not named 
	 * @param s The ensured property
	 **/
	/*@
	  @ requires s != null;
	  @ requires t != null;
	  @*/
	public Exsures(Type t, String name, Expression s) {
		exceptionType = t;
		expression = s;
		// create a field if the exsure clause use a named exception
		if (name != null) {
			exceptionField = new Field(new ParsedItem(), t, name);
		}
	}

	public Object clone() {
		return new Exsures(
			exceptionType,
			exceptionField,
			(Expression) expression.clone());
	}

	boolean equals(Exsures e) {
		return exceptionType.equals(e.exceptionType)
			&& expression.equals(e.expression);
	}

	/*@
	  @ requires c != null;
	  @*/
	public void link(IJml2bConfiguration config, LinkContext c)
		throws Jml2bException {
		if (hasField()) {
			// link the field (do not link the type, since it is linked
			// by the field).
			exceptionField.link(config, c);

			// add the new field to the list of variables
			c.linkVars.pushVars();
			c.linkVars.add(getField());

			expression.link(config, c);

			// remove the field from the variable list
			c.linkVars.popVars();
		} else {
			// link the type
			exceptionType.link(config, c);
			// link the statement
			expression.link(config, c);
		}
	}

	/*@
	  @ requires c != null;
	  @*/
	public int linkStatements(IJml2bConfiguration config, LinkContext c)
		throws Jml2bException {
		if (hasField()) {
			// link the field (do not link the type, since it is linked
			// by the field).
			exceptionField.linkStatements(config, c);

			// add the new field to the list of variables
			c.linkVars.pushVars();
			c.linkVars.add(getField());

			expression.linkStatements(config, c);

			// remove the field from the variable list
			c.linkVars.popVars();
		} else {
			// link the type
			exceptionType.linkStatements(config, c);
			// link the statement
			expression.linkStatements(config, c);
		}
		return 0;
	}

	public Type typeCheck(IJml2bConfiguration config, LinkContext c)
		throws Jml2bException {
		Type t;
		if (hasField()) {
			// add the new field to the list of variables
			c.linkVars.pushVars();
			c.linkVars.add(getField());

			t = expression.typeCheck(config, c);

			// remove the field from the variable list
			c.linkVars.popVars();
		} else {
			// link the statement
			t = expression.typeCheck(config, c);
		}
		if (!t.isBoolean())
			throw new TypeCheckException(
				"An exsures clause should contain a boolean and not a "
					+ t.toJava(),
				expression);

		return null;

	}

	/**
	 * Collects all the indentifier of the clause to give them an index in 
	 * the identifer array. This array is then analyzed to give short name when 
	 * it is possible to identifiers.
	 * @see jml2b.pog.IdentifierResolver#bIdents
	 **/
	public void processIdent() {
		if (exceptionField != null)
			exceptionField.nameIndex =
				IdentifierResolver.addIdent(exceptionField);
		expression.processIdent();
	}

	/**
	 * Instancie the clause.
	 * More <a href="{@docRoot}/jml2b/structure/java/doc-files/instancie.html"> 
	 * informations</a> on instancie.
	 * @return the instanciated exsures clause
	 **/
	public Exsures instancie() {
		expression = (Expression) expression.instancie();
		return this;
	}

	public Exsures renameParam(Parameters signature, Parameters newSignature) {
		expression = expression.renameParam(signature, newSignature);
		return this;
	}

	String emit() {
		return "("
			+ exceptionType.toJava()
			+ " "
			+ (exceptionField != null ? exceptionField.getName() : "")
			+ ") "
			+ expression.toJava(0);
	}

	/**
	 * Returns whether the exsures clause declares a field
	 **/
	/*@
	  @ ensures \result == (exceptionField != null);
	  @*/
	private boolean hasField() {
		return exceptionField != null;
	}

	public void setParsedItem(ParsedItem pi) {
		if (exceptionField != null)
			exceptionField.setParsedItem(pi);
		exceptionType.setParsedItem(pi);
		expression.setParsedItem(pi);
	}

	Expression getNormalized() {
		if (exceptionField == null)
			return expression;
		return new QuantifiedExp(
			JmlDeclParserTokenTypes.QUANTIFIED_EXPR,
			"\forall",
			new QuantifiedVar(
				(ParsedItem) exceptionField,
				exceptionField,
				null),
			expression);
	}

	/**
	 * Returns the field declared into the exsures clause.
	 * @return <code>exceptionField</code>
	 **/
	public Field getField() {
		return exceptionField;
	}

	/**
	 * Returns the type of the exception.
	 * @return <code>exceptionType</code>
	 */
	public Type getExceptionType() {
		return exceptionType;
	}

	/**
	 * Returns the property ensured by this <i>exsures</i> clause.
	 * @return <code>expression</code>
	 **/
	public Expression getExpression() {
		return expression;
	}

	static final long serialVersionUID = -1386643750550948016L;

	public String toJava(int indent) {
		String res = "(";
		res += exceptionType.toJava();
		if (exceptionField != null)
			res += exceptionField.getName();
		res += ") ";
		res += expression.toJava(indent + res.length()) + ";";
		return res;

	}

}
