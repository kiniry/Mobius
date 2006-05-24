//******************************************************************************
/* Copyright (c) 2002, 2003 GEMPLUS Software Research Labs. All Rights Reserved.
/* Copyright (c) 2003, 2004 INRIA. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: Field.java
/*
/********************************************************************************
/* Warnings/Remarks:
/*******************************************************************************/
package jml2b.structure.java;

import java.io.Serializable;

import jml.LineAST;
import jml2b.IJml2bConfiguration;
import jml2b.exceptions.InternalError;
import jml2b.exceptions.Jml2bException;
import jml2b.exceptions.ParseException;
import jml2b.link.LinkContext;
import jml2b.pog.util.IdentifierResolver;
import jml2b.structure.AField;
import jml2b.structure.statement.Expression;
import jml2b.structure.statement.TTypeExp;
import antlr.collections.AST;

/** 
 * Class representing fields. It stores the name and the type of a
 * field or variable.
 * 
 * This class is also used to represent local variables. In that case,
 * the modifiers can be null.
 *   
 * @author A. Requet
 */
public class Field extends AField implements Serializable {
	/** 
	 * AST containing potential assign clauses
	 */
	private /*@ spec_public */
	Expression assign;

	/** 
	 * Name of the field
	 */
	private String name;

	/** 
	 * Type of the field.
	 */
	private Type type;

	/*@
	  @ private invariant type != null;
	  @*/

	public Field() {
		
	}
	
	//@ requires t != null;
	public Field(ParsedItem pi, Modifiers m, Type t, String n, Expression a) {
		super(pi, m);
		type = t;
		name = n;
		if (a == null) {
			assign = getDefaultInitialiser();
		} else {
			assign = a;
		}
	}

	//@ requires t != null;
	public Field(ParsedItem pi, Type t, String n) {
		super(pi, (Modifiers) null);
		type = t;
		name = n;
	}

	/** 
	 * Parses the AST. This method has been removed since fields are parsed
	 * using the <code>VarDeclParser</code> class.
	 * 
	 * @deprecated The <code>VarDeclParser</code> class should be used
	 *     instead of this method.
	 */
	//@ requires a != null;
	public AST parse(JmlFile jmlFile, AST a) throws Jml2bException {
		throw new ParseException(
			jmlFile,
			(LineAST) a,
			"This function is usually not called");
	}

	public void link(IJml2bConfiguration config, LinkContext f)
		throws Jml2bException {

		type.link(config, f);
		if (assign != null) {
			if (getDefiningClass() == null || !((Class) getDefiningClass()).isExternal()) {
				assign.link(config, f);
			}
		}
	}

	public int linkStatements(IJml2bConfiguration config, LinkContext f)
		throws Jml2bException {
		type.linkStatements(config, f);
		if (assign != null) {
			if (((Class) getDefiningClass()) == null
				|| !((Class) getDefiningClass()).isExternal()
				|| isExpanded()) {
				assign.linkStatements(config, f);
			}
		}
		return 0;
	}

	/** 
	 * Returns the Expression object corresponding to the assign clause of
	 * this field
	 * The assign clause of a field corresponds to its initialisation, when
	 * an initialisation is given during the declaration of the field.
	 * 
	 * @return Expression the expression object corresponding to the 
	 *    assign clause of the field. 
	 */
	public Expression getAssign() {
		return assign;
	}

	/**
	 * Sets the <code>Expression</code> object corresponding to the assign
	 * clause of the field.
	 * The assign clause of a field corresponds to its initialisation, when
	 * an initialisation is given during the declaration of the field.
	 * 
	 * @param a the expression corresponding to the assign clause.
	 */
	//@ private modifies assign;
	public void setAssign(Expression a) {
		assign = a;
	}

	/**
	 * Indicates wether the field correspond to a local variable or 
	 * to a parameter.
	 * 
	 * @return boolean
	 */
	public boolean isLocal() {
		return ((Class) getDefiningClass()) == null;
	}

	public Expression getDefaultInitialiser() {
		switch (type.getTag()) {
			case Type.T_BOOLEAN :
				return Expression.getFalse();
			case Type.T_INT :
			case Type.T_SHORT :
			case Type.T_BYTE :
			case Type.T_CHAR :
			case Type.T_LONG :
				return Expression.getZero();
			case Type.T_DOUBLE :
			case Type.T_FLOAT :
				return Expression.getZero();
			case Type.T_REF :
			case Type.T_ARRAY :
				return Expression.getNull();
			case Type.T_TYPE :
				{
					// default initialiser for type: object
					return new TTypeExp(
						Type.createUnlinkedClass("java.lang.Object"));
				}
			case Type.T_VOID :
				// pas d'initialiseur pour void
				return null;
			default :
				throw new InternalError(
					"Unhandled case in getDefaultInitialiser: "
						+ type.getTag());
		}
	}

	/**
	 * Returns the name of the field.
	 * 
	 * @return String the name of the field.
	 */
	public String getName() {
		return name;
	}

	/**
	 * Returns the B name of the field.
	 * 
	 * @return String a B identifier corresponding to the name fo the field.
	 */
	public String getBName() {
		if (nameIndex < 0) {
			throw new jml2b.exceptions.InternalError(
				"NamedNode.getBName() " + nameIndex + " " + getName());
		}
		return IdentifierResolver.bName(nameIndex);
	}

	/**
	 * Retursn the type of the field.
	 * 
	 * @return Type the type of the field.
	 */
	/*@
	  @ ensures \result != null;
	  @*/
	public Type getType() {
		return type;
	}

	//@ requires vardecl != null;
	public static Field[] parseVarDecl(
		JmlFile jmlFile,
		AST vardecl,
		Modifiers mods)
		throws Jml2bException {
		VarDeclParser parser = new VarDeclParser();
		vardecl = parser.parse(jmlFile, vardecl);
		return parser.getArray();
	}

	public boolean isExpanded() {
		return getModifiers() != null
			&& getModifiers().isStatic()
			&& getModifiers().isFinal()
			&& getAssign() != null
			&& getAssign().isConstant()
			&& getType().getTag() != Type.T_LONG;
	}

	public String emit() {
		String s = "    ";
		if (getModifiers() != null && ((Modifiers) getModifiers()).isJml())
			s += "//@";
		s += (getModifiers() != null ? getModifiers().emit() : "");
		s += type.toJava() + " ";
		s += name + " = ";
		s += assign.toJava(0);
		s += ";\n\n";
		return s;
	}

	public void setParsedItem(ParsedItem pi) {
		change(pi);
	}

	static final long serialVersionUID = -7938980969842210873L;
}