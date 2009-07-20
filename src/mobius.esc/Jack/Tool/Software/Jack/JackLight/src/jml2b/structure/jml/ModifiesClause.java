//******************************************************************************
/* Copyright (c) 2002, 2003 GEMPLUS Software Research Labs. All Rights Reserved.
/* Copyright (c) 2003, 2004 INRIA. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: ModifiesClause.java
/*
/*******************************************************************************
/* Warnings/Remarks:
/******************************************************************************/
package jml2b.structure.jml;

import java.util.Collection;
import java.util.HashSet;
import java.util.Vector;

import jml.JmlDeclParserTokenTypes;
import jml.LineAST;
import jml2b.IJml2bConfiguration;
import jml2b.exceptions.ErrorHandler;
import jml2b.exceptions.Jml2bException;
import jml2b.exceptions.PogException;
import jml2b.formula.IFormToken;
import jml2b.link.LinkContext;
import jml2b.link.LinkInfo;
import jml2b.link.TypeCheckable;
import jml2b.structure.java.Class;
import jml2b.structure.java.JmlFile;
import jml2b.structure.java.Parameters;
import jml2b.structure.java.ParsedItem;
import jml2b.structure.statement.Expression;
import antlr.collections.AST;

/**
 * This class describes the content of a modifies clause.
 * A modifies clause can be:
 * <UL>
 * <li> <code>\nothing</code>
 * <li> <code>\everything</code>
 * <li> a list of modified variable that can be
 *  <UL>
 *  <li> a identifier: <code>a, a.b</code>
 *  <li> an array element: <code>a[b]</code>
 *  <li> some elements of an array: <code>a[b..c]</code>
 *  <li> all the element of an array: <code>a[*]</code>
 *  </UL>
 * </UL>
 * @author L. Burdy
 */
public abstract class ModifiesClause
	extends ParsedItem
	implements TypeCheckable, JmlDeclParserTokenTypes, IFormToken {

	/**
	 * Default constructor. (For invocation by subclass constructors, typically
	 * implicit.)
	 **/
	ModifiesClause() {
	}

	/**
	 * Constructs a <code>ModifiesClause</code> as a <i>parsed item</i>
	 * @param pi <i>parsed item</i> to take into account to construct this new
	 * <i>parsed item</i>.
	 **/
	ModifiesClause(ParsedItem pi) {
		super(pi);
	}

	/**
	 * Constructs a <code>ModifiesClause</code> as a <i>parsed item</i>
	 * @param jf <i>jml file</i> to take into account to construct this new
	 * <i>parsed item</i>.
	 * @param a <i>AST</i> node to take into account to construct this new
	 * <i>parsed item</i>.
	 **/
	ModifiesClause(JmlFile jf, AST a) throws Jml2bException {
		super(jf, a);
	}

	/**
	 * Create a concrete modifies clause depending of the <code>AST</code> 
	 * content
	 * @param jf <i>JML file</i> currently parsed
	 * @param a <code>AST</code> tree currently parsed
	 * @return a new concrete modifies clause
	 **/
	public static ModifiesClause create(JmlFile jf, AST a)
		throws Jml2bException {
		switch (a.getType()) {
			case T_NOTHING :
				return new ModifiesNothing(jf, a);
			case T_EVERYTHING :
				return new ModifiesEverything(jf, a);
			case T_FIELDS_OF :
				ErrorHandler.warning(
					jf,
					((LineAST) a).line,
					((LineAST) a).column,
					"\\fields_of keyword is not handled");
				return null;
			case COMMA :
				if (a.getFirstChild().getNextSibling().getType() == T_FIELDS_OF) {
					ErrorHandler.warning(
						jf,
						((LineAST) a).line,
						((LineAST) a).column,
						"\\fields_of keyword is not handled");
					return ModifiesClause.create(jf, a.getFirstChild());
				}
			default :
				return new ModifiesList(jf, a);
		}
	}

	/**
	 * Clones the object.
	 * @return the cloned object
	 **/
	public abstract Object clone();

	/**
	 * Instancie the <i>modifies clause</i>.
	 * More <a href="{@docRoot}/jml2b/structure/java/doc-files/instancie.html"> 
	 * informations</a> on instancie.
	 **/
	public abstract void instancie(IJml2bConfiguration config)
		throws PogException;

	/** 
	 * Replace <code>this</code> with the parameter in the <i>modifies clause</i>.
	 * @param b expression on which the metohd is called.
	 **/
	public abstract void instancie(Expression b, IJml2bConfiguration config)
		throws PogException;

	/**
	 * Renames the parameter in the <i>modifies clause</i>.
	 * @param signature the signature of the called method
	 * @param newSignature the list of new names
	 * @return the current <i>modified clause</i> renamed
	 * @throws PogException
	 * @see Proofs#renameParam(Parameters, Vector)
	 **/
	public abstract ModifiesClause renameParam(
		IJml2bConfiguration config,
		Parameters signature,
		Vector newSignature)
		throws PogException;

	/**
	 * Links the content of the clause.
	 * @param f context for link
	 * @return the calculated link informations
	 * @throws Jml2bException
	 **/
	public abstract LinkInfo linkStatements(
		IJml2bConfiguration config,
		LinkContext f)
		throws Jml2bException;

	/**
	 * Collects all the indentifier of the clause to give them an index in the 
	 * identifer array. This array is then analyzed to give short name when it
	 * is possible to identifiers.
	 * @see jml2b.pog.IdentifierResolver#bIdents
	 **/
	public abstract void processIdent();

	/**
	 * Complete the modifies with modified store-ref issued from depends 
	 * clauses.
	 * @param c The defining class of the depends clauses
	 **/
	public abstract void addDepends(IJml2bConfiguration config, Class c)
		throws PogException;

	/**
	 * @param l
	 * @return ModifiesClause
	 */
	public abstract ModifiesClause completeModifiesWithFields(ModifiesList l);

	public abstract void setParsedItem(ParsedItem pi);

	public Collection getFields() {
		return new HashSet();
	}

}
