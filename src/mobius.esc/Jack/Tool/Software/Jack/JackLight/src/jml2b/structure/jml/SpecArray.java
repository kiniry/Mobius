//******************************************************************************
/* Copyright (c) 2002, 2003 GEMPLUS Software Research Labs. All Rights Reserved.
/* Copyright (c) 2003, 2004 INRIA. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: SpecArray.java
/*
/*******************************************************************************
/* Warnings/Remarks:
/******************************************************************************/
package jml2b.structure.jml;

import java.util.Vector;

import jml.JmlDeclParserTokenTypes;
import jml2b.IJml2bConfiguration;
import jml2b.exceptions.Jml2bException;
import jml2b.exceptions.PogException;
import jml2b.formula.IFormToken;
import jml2b.link.LinkContext;
import jml2b.link.LinkInfo;
import jml2b.link.TypeCheckable;
import jml2b.pog.lemma.FormulaWithPureMethodDecl;
import jml2b.structure.java.Field;
import jml2b.structure.java.JmlFile;
import jml2b.structure.java.ParsedItem;
import jml2b.structure.statement.Expression;
import antlr.collections.AST;

/**
 * This class defines the possible indexes set of an array in the modifies 
 * clause. 
 * It can be:
 * <UL>
 * <li> an index <code>a</code>
 * <li> an index interval <code>a..b</code>
 * <li> all the indexes <code>*</code>
 * </UL>
 * @author L. Burdy
 **/
public abstract class SpecArray
	extends ParsedItem
	implements JmlDeclParserTokenTypes, IFormToken, TypeCheckable {

	/**
	 * Constructs an empty indexes set corresponding to a parsed item.
	 * @param jf The current JML file
	 * @param tree The tree corresponding to this modifies
	 **/
	SpecArray(JmlFile jf, AST tree) {
		super(jf, tree);
	}

	/**
	 * Constructs an empty indexes set corresponding to a parsed item.
	 * @param pi The parsed item
	 **/
	SpecArray(ParsedItem pi) {
		super(pi);
	}

	/**
	 * Creates an indexes set.
	 * This variable can be a single index, a index interval or all the indexes 
	 * depending of the token of the tree.
	 * @param jf The current JML file
	 * @param a The tree corresponding to this modifies
	 * @return The created indexes set
	 * @throws Jml2bException
	 **/
	static SpecArray create(JmlFile jf, AST a) throws Jml2bException {
		switch (a.getType()) {
			case DOT_DOT :
				return new SpecArrayDotDot(jf, a);
			case STAR_ELEMS :
				return new SpecArrayStar(jf, a);
			default :
				return new SpecArrayExpr(jf, a);
		}
	}

	/**
	 * Clones the indexes set.
	 * @return the cloned indexes set
	 **/
	public abstract Object clone();

	/**
	 * Returns the formula corresponding to this indexes set but not as a set.
	 * @return the formula corresponding to the set.
	 **/
	abstract FormulaWithPureMethodDecl getFormula(IJml2bConfiguration config)
		throws PogException;

	/**
	 * Returns the formula corresponding to this indexes set as a set
	 * @param m The current modified array (usefull to calculate the formula 
	 * corresponding to all the index of an array)
	 * @return the formula corresponding to the set with type set.
	 **/
	abstract FormulaWithPureMethodDecl getSet(IJml2bConfiguration config, Modifies m)
		throws PogException;

	/**
	 * Converts the setto Java
	 * @return the string as it was originally in the source
	 **/
	abstract String toJava(int indent);

	abstract LinkInfo linkStatement(IJml2bConfiguration config, LinkContext f)
		throws Jml2bException;

	/**
	 * Instancie the indexes set.
	 * More <a href="{@docRoot}/jml2b/structure/java/doc-files/instancie.html"> 
	 * informations</a> on instancie.
	 * @return the instanciated indexes set
	 **/
	abstract SpecArray instancie();

	/** 
	 * Replace <code>this</code> with the parameter in the set.
	 * @param b expression on which the method is called.
	 **/
	abstract void instancie(Expression b);

	/**
	 * Substitutes two fields.
	 * @param config The current configuration
	 * @param m The current modified array
	 * @param a The field to substitute
	 * @param b The new field
	 * @return The substituted modifies
	 * @throws PogException
	 **/
	abstract SpecArray sub(
		IJml2bConfiguration config,
		Modifies m,
		Field a,
		Field b)
		throws PogException;

	/**
	 * Collects all the indentifier of the set to give them an index in the 
	 * identifer array. This array is then analyzed to give short name when it
	 * is possible to identifiers.
	 * @see jml2b.pog.IdentifierResolver#bIdents
	 **/
	abstract void processIdent();

	/**
	 * Returns the set of parsed items that correspond to this expression
	 * @return the set of parsed item that correspond to the complete 
	 * expression 
	 **/
	abstract Vector getParsedItems();

	abstract void setParsedItem(ParsedItem pi);

}
