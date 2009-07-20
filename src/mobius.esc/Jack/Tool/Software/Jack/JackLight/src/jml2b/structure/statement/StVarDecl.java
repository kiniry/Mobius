//******************************************************************************
/* Copyright (c) 2002, 2003 GEMPLUS Software Research Labs. All Rights Reserved.
/* Copyright (c) 2003, 2004 INRIA. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: StVarDecl
/*
/*******************************************************************************
/* Warnings/Remarks:
/*  09/26/2003 : Simplify integration achieved
/******************************************************************************/
package jml2b.structure.statement;

import java.util.Enumeration;
import java.util.Vector;

import jml2b.IJml2bConfiguration;
import jml2b.exceptions.Jml2bException;
import jml2b.link.LinkContext;
import jml2b.link.LinkInfo;
import jml2b.link.LinkUtils;
import jml2b.pog.util.IdentifierResolver;
import jml2b.structure.java.Class;
import jml2b.structure.java.Field;
import jml2b.structure.java.JmlFile;
import jml2b.structure.java.Type;
import jml2b.structure.java.VarDeclParser;
import antlr.collections.AST;

/**
 * This class implements a set of local field declaration statement
 * @author L. Burdy, A. Requet
 **/
public class StVarDecl extends Statement {

	/**
	 * The set of declared {@link Field}
	 **/
	private Vector localVariables;

	/*@
	  @ private invariant localVariables != null 
	  @ private invariant localVariables.elementType <: \type(Field)
	  @*/

	/**
	 * Constructs a statement that will be filled by the parse method.
	 * @param jf The parsed file
	 * @param tree The current tree node
	 **/
	protected StVarDecl(JmlFile jf, AST tree) {
		super(jf, tree);
		localVariables = new Vector();
	}

	public String emit() {
		String s = "";
		Enumeration e = localVariables.elements();
		while (e.hasMoreElements()) {
			Field element = (Field) e.nextElement();
			s += element.emit();
		}
		return s;
	}

	/**
	 * Constructs a statement from a set of fields
	 * @param localVariables The set of fields.
	 **/
	/*@
	  @ requires localVariables != null 
	  @       && localVariables.elementType <: \type(Field);
	  @*/
	public StVarDecl(final Vector localVariables) {
		super();
		this.localVariables = localVariables;
	}

	public AST parse(AST tree) throws Jml2bException {
		if (tree.getType() == LITERAL_final || tree.getType() == GHOST)
			tree = tree.getNextSibling();
		VarDeclParser parser = new VarDeclParser();
		parser.parse(getJmlFile(), tree);
		Enumeration e = parser.getVars();
		while (e.hasMoreElements()) {
			Field f = (Field) e.nextElement();
			localVariables.add(f);
		}
		return tree.getNextSibling();
	}

	public LinkInfo linkStatement(IJml2bConfiguration config, LinkContext f)
		throws Jml2bException {
		// add the local variables declaration to the current 
		// block
		LinkUtils.linkEnumeration(config, localVariables.elements(), f);
		// add local variable to table before linking statements,
		// since the currently linked local variables mey be used
		// in the assign clause.        
		f.linkVars.add(localVariables);

		LinkUtils.linkStatements(config, localVariables.elements(), f);
		return null;
	}

	public Type typeCheck(IJml2bConfiguration config, LinkContext f)
		throws Jml2bException {
		return null;
	}

	public Statement jmlNormalize(
		IJml2bConfiguration config,
		Class definingClass) {
		Enumeration e = localVariables.elements();
		while (e.hasMoreElements()) {
			Field f = (Field) e.nextElement();
			f.nameIndex = IdentifierResolver.addIdent(f);
			f.getAssign().processIdent();
			f.setAssign((Expression) f.getAssign().instancie());
		}
		return this;
	}

	public void collectCalledMethod(Vector calledMethod) {
		Enumeration e = localVariables.elements();
		while (e.hasMoreElements()) {
			Field f = (Field) e.nextElement();
			f.getAssign().collectCalledMethod(calledMethod);
		}
	}

	public void getAssert(Vector asser) {
		Enumeration e = localVariables.elements();
		while (e.hasMoreElements()) {
			Field f = (Field) e.nextElement();
			f.getAssign().getAssert(asser);
		}
	}

	public void getSpecBlock(Vector asser) {
		Enumeration e = localVariables.elements();
		while (e.hasMoreElements()) {
			Field f = (Field) e.nextElement();
			f.getAssign().getSpecBlock(asser);
		}
	}

	public void getLoop(Vector asser) {
		Enumeration e = localVariables.elements();
		while (e.hasMoreElements()) {
			Field f = (Field) e.nextElement();
			f.getAssign().getLoop(asser);
		}
	}

	static final long serialVersionUID = -5757089589800261606L;
}
