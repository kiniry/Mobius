///******************************************************************************
//* Copyright (c) 2002, 2003 GEMPLUS Software Research Labs. All Rights Reserved.
//*------------------------------------------------------------------------------
//* Name: VarDeclParser.java
//*
//********************************************************************************
//* Warnings/Remarks:
//*******************************************************************************/
package jml2b.structure.java;

import java.util.Enumeration;
import java.util.Vector;

import jml.JmlDeclParserTokenTypes;
import jml.LineAST;
import jml2b.IJml2bConfiguration;
import jml2b.exceptions.Jml2bException;
import jml2b.exceptions.ParseException;
import jml2b.link.LinkContext;
import jml2b.link.LinkUtils;
import jml2b.link.Linkable;
import jml2b.structure.statement.Expression;
import jml2b.util.Profiler;
import antlr.collections.AST;

/** 
 * Parser used for parsing <code>VAR_DECL</code> clauses.
 * 
 * @author A. Requet
 */
public class VarDeclParser extends Profiler implements Linkable {
	Type type;
	Modifiers mods;

	/** 
	 * Vector containing the parsed variables. All the elements stored inside
	 * are of type Field.
	 */
	Vector parsedVars;

	/*@
	  @ invariant parsedVars != null;
	  @*/

	/** 
	 * Creates a <code>VarDeclParser</code> initialised with the given AST.
	 */
	public VarDeclParser() {
		parsedVars = new Vector();
	}

	/**
	 * Creates a new instance using the given modifier for the parsed
	 * variables.
	 * 
	 * @param m the modifiers that will be used for the parsed variables.
	 */
	public VarDeclParser(Modifiers m) {
		parsedVars = new Vector();
		mods = m;
	}

	/**
	 * Sets the modifiers that will be used for the parsed variables.
	 * 
	 * @param m the modifiers that will be used for the parsed variables.
	 */
	/*@ modifies mods; */
	void setModifier(Modifiers m) {
		mods = m;
	}

	/**
	 * Returns an enumeration of the parsed variables.
	 * 
	 * @return Enumeration an enumeration of the parsed variables. 
	 *     The enumerated elements are of type <code>Field</code>
	 * @see Field
	 */
	public Enumeration getVars() {
		return parsedVars.elements();
	}

	/** 
	 * Return the underlying vector.
	 * @return the vector containing the parsed variables. The stored 
	 *     elements are of type <code>Field</code>
	 * @see Field  
	 */
	Vector getVector() {
		return parsedVars;
	}

	/**
	 * Returns the parsed variables as an array of fields.
	 * 
	 * @return Field[] The parsed variables.
	 */
	public Field[] getArray() {
		Field[] res;
		int count = parsedVars.size();
		res = new Field[count];

		//@ loop_invariant true;
		//@ loop_exsures (RuntimeException) false;
		for (int i = 0; i < count; ++i) {
			res[i] = (Field) parsedVars.get(i);
		}

		return res;
	}

	/** 
	 * Returns the number of variables stored in the array.
	 * 
	 * @return the number of parsed variables.
	 */
	public int getFieldCount() {
		return parsedVars.size();
	}

	//@ requires ast != null;
	//@ modifies type;
	public AST parse(JmlFile jmlFile, AST ast)
		throws Jml2bException {
		AST current = ast.getFirstChild();

		// create the basic type and parse it
		type = new Type(jmlFile, current);

		current = type.parse(current);

		/* now useless
		   current = current.getNextSibling();
		
		   // parse the dimensions if needed
		   if(current.getType() == JmlDeclParserTokenTypes.DIMS) {
		   // increase the dimension of the type	    
		   type = Type.addDims(current, type);
		   current = current.getNextSibling();
		   }
		*/

		parseDeclList(jmlFile, current);
		return ast.getNextSibling();
	}

	public void link(IJml2bConfiguration config, LinkContext f)
		throws Jml2bException {
		LinkUtils.linkEnumeration(config, getVars(), f);
	}

	public int linkStatements(IJml2bConfiguration config, LinkContext f)
		throws Jml2bException {
		return LinkUtils.linkStatements(config, getVars(), f);
	}

	/** parse the variables declarations
	 */
	/*@
	  @ requires var != null;
	  @ requires \typeof(var) <: \type(LineAST);
	  @*/
	private AST parseDeclList(
		JmlFile jmlFile,
		AST var)
		throws Jml2bException {
		AST tmp;

		switch (var.getType()) {
			case JmlDeclParserTokenTypes.COMMA :
				// a comma has two childrens corresponding to the two sides
				// of the comma
				tmp = var.getFirstChild();
				tmp = parseDeclList(jmlFile, tmp);
				tmp = parseDeclList(jmlFile, tmp);

				return var.getNextSibling();

			case JmlDeclParserTokenTypes.IDENT :
				return parseDecl(jmlFile, var);

			default :
				throw new ParseException(
					jmlFile,
					(LineAST) var,
					"parseVarList: unexpected token");
		}
	}

	/** 
	 * parse the given variable and initialiser
	 **/
	//@ requires ident != null;
	private AST parseDecl(
		JmlFile jmlFile,
		AST ident)
		throws Jml2bException {
		ParsedItem b = new ParsedItem(jmlFile, ident);
		//        b.setX(ident);
		String field_name = ident.getText();
		//        b.setY(field_name.length());
		Type field_type = type;
		Expression assign = null;

		AST res = ident.getNextSibling();

		// if additional dimensions are given for this field, increase the 
		// count dimension
		if (res != null && res.getType() == JmlDeclParserTokenTypes.DIMS) {
			field_type = Type.addDims(jmlFile, res, field_type);
			res = res.getNextSibling();
		}

		if (res != null && res.getType() == JmlDeclParserTokenTypes.ASSIGN) {
			// create the appropriate statement
			assign = Expression.createE(jmlFile, res.getNextSibling());
			res = assign.parse(res.getNextSibling());
		}

		if (res != null
			&& res.getType() == JmlDeclParserTokenTypes.INITIALLY) {
			// create the appropriate statement
			assign = Expression.createE(jmlFile, res.getFirstChild());
			res = assign.parse(res.getFirstChild());
		}

		Field f = new Field(b, mods, field_type, field_name, assign);
		//        f.setJmlFile(jmlFile);
		//        f.setBox(b);
		parsedVars.add(f);

		return res;
	}
}