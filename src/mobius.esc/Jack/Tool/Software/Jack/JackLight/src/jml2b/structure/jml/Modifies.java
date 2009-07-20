//******************************************************************************
/* Copyright (c) 2002, 2003 GEMPLUS Software Research Labs. All Rights Reserved.
/* Copyright (c) 2003, 2004 INRIA. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: Modifies
/*
/*******************************************************************************
/* Warnings/Remarks:
/******************************************************************************/
package jml2b.structure.jml;

import java.util.Vector;

import jml.JmlDeclParserTokenTypes;
import jml.LineAST;
import jml2b.IJml2bConfiguration;
import jml2b.exceptions.ErrorHandler;
import jml2b.exceptions.InternalError;
import jml2b.exceptions.Jml2bException;
import jml2b.exceptions.PogException;
import jml2b.formula.Formula;
import jml2b.formula.IFormToken;
import jml2b.link.LinkContext;
import jml2b.link.LinkInfo;
import jml2b.link.TypeCheckable;
import jml2b.pog.lemma.FormulaWithPureMethodDecl;
import jml2b.structure.AField;
import jml2b.structure.java.Field;
import jml2b.structure.java.JmlFile;
import jml2b.structure.java.ParsedItem;
import jml2b.structure.java.Type;
import jml2b.structure.statement.Expression;
import antlr.collections.AST;

/**
 * This class represents a modified variable.
 * This variable can be 
 *  <UL>
 *  <li> a identifier: <code>a, a.b</code>
 *  <li> an array element: <code>a[b]</code>
 *  <li> some elements of an array: <code>a[b..c]</code>
 *  <li> all the element of an array: <code>a[*]</code>
 *  </UL>
 * @author L. Burdy
 */
public abstract class Modifies
	extends ParsedItem
	implements JmlDeclParserTokenTypes, IFormToken, TypeCheckable {

	/**
	 * The type of the modified variable.
	 **/
	private Type stateType;

	/**
	 * Constructs an empty modified variable corresponding to a parsed item.
	 * @param jf The current JML file
	 * @param a The tree corresponding to this modifies
	 **/
	Modifies(JmlFile jf, AST tree) {
		super(jf, tree);
	}

	/**
	 * Constructs an empty modified variable corresponding to a parsed item.
	 * @param pi The parsed item
	 * @param t The type of the parsed item
	 **/
	Modifies(ParsedItem pi, Type t) {
		super(pi);
		stateType = t;
	}

	//    /**
	//     * Constructs an empty modified variable corresponding to a parsed item.
	//     * @param pi The parsed item
	//     **/
	//    Modifies(ParsedItem pi) {
	//        super(pi);
	//    }

	/**
	 * Creates a modified variable.
	 * This variable can be a static field, a member field or an array at
	 * an index depending of the token of the tree.
	 * @param jf The current JML file
	 * @param a The tree corresponding to this modifies
	 * @return The created modifies variable
	 * @throws Jml2bException
	 * @throws InternalError when the tree is corrupted
	 **/
	static Modifies create(JmlFile jf, AST a) throws Jml2bException {
		switch (a.getType()) {
			case IDENT :
				return new ModifiesIdent(jf, a);
			case LBRACK :
				return new ModifiesLbrack(jf, a);
			case DOT :
				return new ModifiesDot(jf, a);
			case T_FIELDS_OF :
				ErrorHandler.warning(
					jf,
					((LineAST) a).line,
					((LineAST) a).column,
					"\\fields_of keyword is not handled");
				return null;
			default :
				throw new InternalError("Modifies.create " + a.getType());
		}
	}

	/**
	 * Clones the modified variable.
	 * @return the cloned modified variable
	 **/
	public abstract Object clone();

	public abstract boolean equals(IJml2bConfiguration config, Modifies m);

	/**
	 * Returns the formula corresponding to the restriction to be applied to
	 * a member field restricted to the current instances set.
	 * @param config The current configuration
	 * @param f The field to restrict.
	 * @return the restriction to applied to the domain of the member field.
	 **/
	abstract FormulaWithPureMethodDecl getModifiedInstances(IJml2bConfiguration config, AField f);

	/**
	 * Returns the formula corresponding to the restriction to be applied to 
	 * the variable xxxelements with type corresponding to tag.
	 * @param config The current configuration
	 * @param tag: tag of the xxxelements to restrict.
	 * @return a restriction to applied to the domain of the corresponding
	 * xxxelements variable.
	 * @throws PogException
	 **/
	abstract FormulaWithPureMethodDecl restrictElement(IJml2bConfiguration config, int tag)
		throws PogException;

	/**
	 * Return the formula corresponding to the restriction to be applied to
	 * the domain of the <code>xxxelements(q)</code> function.
	 * @param config The current configuration
	 * @return the restriction to applied to the domain of 
	 * <code>xxxelements(q)</code>.
	 * @throws PogException
	 **/
	abstract FormulaWithPureMethodDecl getModifiedIndexes(
		IJml2bConfiguration config,
		int tag,
		Formula q)
		throws PogException;

	/**
	 * Returns whether a field is modified by this modified variable
	 * @param f The tested field
	 * @return <code>true</code> if the field is modified by this instance, 
	 * <code>false</code> otherwise
	 **/
	abstract boolean is(AField f);


	abstract LinkInfo linkStatements(IJml2bConfiguration config, LinkContext f)
		throws Jml2bException;

	/**
	 * Instancie the <i>modifies clause</i>.
	 * More <a href="{@docRoot}/jml2b/structure/java/doc-files/instancie.html"> 
	 * informations</a> on instancie.
	 * @return the instanciated <i>modifies clause</i>
	 **/
	abstract Modifies instancie();

	/** 
	 * Replace <code>this</code> with the parameter in the <i>modifies clause</i>.
	 * @param b expression on which the method is called.
	 **/
	abstract void instancie(Expression b);

	/**
	 * Substitutes two fields.
	 * @param config The current configuration
	 * @param a The field to substitute
	 * @param b The new field
	 * @return The substituted modifies
	 * @throws PogException
	 **/
	abstract Modifies sub(IJml2bConfiguration config, Field a, Field b)
		throws PogException;

	/**
	 * Collects all the indentifier of the clause to give them an index in the 
	 * identifer array. This array is then analyzed to give short name when it
	 * is possible to identifiers.
	 * @see jml2b.pog.IdentifierResolver#bIdents
	 **/
	abstract void processIdent();

	/**
	 * Returns the formula corresponding to this modified store-ref
	 * @param config The current configuration
	 **/
	abstract FormulaWithPureMethodDecl getFormula(IJml2bConfiguration config)
		throws PogException;

	/**
	 * Returned the modified store ref as a set of modified instances
	 * @param config The current configuration
	 * @return the set of modifies instances corresponding to this store-ref
	 * @throws PogException
	 **/
	abstract FormulaWithPureMethodDecl getSet(IJml2bConfiguration config) throws PogException;

	/**
	  * Returns the set of parsed items that correspond to this expression
	  * @return the set of parsed item that correspond to the complete 
	  * expression 
	  **/
	abstract Vector getParsedItems();

	/**
	 * Return a set of modified store-ref issued from a depends clause.
	 * @param config The current configuration
	 * @param d The depends clause
	 **/
	/*@
	  @ ensures \result != null;
	  @*/
	abstract Vector addDepends(IJml2bConfiguration config, Depends d)
		throws PogException;

	/**
	 * Returns the field that is modified or from which elements are modified
	 **/
	abstract AField getField();

	/**
	 * Returns the instance on which a field is modified
	 **/
	abstract Expression getInstanciation();

	/**
	 * Returns whether the modified field is a member field not instanciated
	 **/
	abstract boolean isMemberNonInstanciated();

	abstract void setParsedItem(ParsedItem pi);

	/**
	 * Returns the stateType.
	 * @return Type
	 */
	final Type getStateType() {
		return stateType;
	}

	/**
	 * Sets the stateType.
	 * @param stateType The stateType to set
	 */
	final void setStateType(Type stateType) {
		this.stateType = stateType;
	}

}
