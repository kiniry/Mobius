//******************************************************************************
/* Copyright (c) 2002, 2003 GEMPLUS Software Research Labs. All Rights Reserved.
/* Copyright (c) 2003, 2004 INRIA. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: ArrayInitializer.java
/*
/*******************************************************************************
/* Warnings/Remarks:
/*  09/26/2003 : Simplify integration achieved
/******************************************************************************/
package jml2b.structure.statement;

import java.io.Serializable;
import java.util.Set;
import java.util.Vector;

import jml.JmlDeclParserTokenTypes;
import jml2b.IJml2bConfiguration;
import jml2b.exceptions.Jml2bException;
import jml2b.exceptions.LanguageException;
import jml2b.exceptions.PogException;
import jml2b.formula.BinaryForm;
import jml2b.formula.ElementsForm;
import jml2b.formula.Formula;
import jml2b.formula.IFormToken;
import jml2b.formula.TTypeForm;
import jml2b.formula.TerminalForm;
import jml2b.link.LinkContext;
import jml2b.link.LinkInfo;
import jml2b.pog.lemma.ExceptionalBehaviourStack;
import jml2b.pog.lemma.FormulaWithSpecMethodDecl;
import jml2b.pog.lemma.Proofs;
import jml2b.pog.substitution.SubArrayElementSingle;
import jml2b.pog.substitution.SubArrayLength;
import jml2b.pog.substitution.SubInstancesSingle;
import jml2b.pog.substitution.SubTmpVar;
import jml2b.pog.substitution.SubTypeofSingle;
import jml2b.structure.java.Field;
import jml2b.structure.java.JmlFile;
import jml2b.structure.java.Modifiers;
import jml2b.structure.java.ParsedItem;
import jml2b.structure.java.Type;
import jml2b.structure.jml.JmlExpression;
import jml2b.util.ModifiableSet;
import jml2b.util.Profiler;
import antlr.collections.AST;

/**
 * This class implements a list of expressions corresponding to an array 
 * initializer.
 * @author L. Burdy, A. Requet
 **/
class ListExp
	extends Profiler
	implements JmlDeclParserTokenTypes, Serializable, IFormToken {

	/**
	 * The current expression
	 **/
	private Expression exp;

	/*@
	  @ private ghost boolean parsed = false;
	  @ invariant parsed ==> exp != null;
	  @ invariant parsed && next != null ==> next.parsed;
	  @*/

	/**
	 * The next element of the list
	 **/
	private ListExp next;

	/**
	 * Clones the list
	 * @return the cloned list
	 **/
	/*@
	  @ requires parsed;
	  @*/
	public Object clone() {
		ListExp res = new ListExp();
		res.exp = (Expression) exp.clone();
		res.next = next == null ? null : (ListExp) next.clone();
		//@ set res.parsed = true;
		return res;
	}

	/**
	 * Returns whether two list are equal.
	 * @param l The tested list
	 * @return <code>true</code> if the list equals the parameter, 
	 * <code>false</code> otherwise
	 **/
	/*@
	  @ requires parsed && l != null && l.parsed;
	  @*/
	public boolean equals(ListExp l) {
		return exp.equals(l.exp)
			&& (next == null
				? l.next == null
				: (l.next != null && next.equals(l.next)));
	}

	/**
	 * Parses an <code>AST</code> tree in order to instanciate the fields.
	 * @param jmlFile The current JML file
	 * @param tree <code>AST</code> tree containing the statement
	 * @return the remaining non parsed tree.
	 * @throws Jml2bException when a parse error occurs.
	 **/
	/*@
	  @ modifies exp, next;
	  @ ensures exp != null && parsed;
	  @*/
	AST parse(JmlFile jmlFile, AST tree) throws Jml2bException {
		exp = Expression.createE(jmlFile, tree);
		AST subtree = exp.parse(tree);
		if (subtree.getType() != RCURLY) {
			next = new ListExp();
			return next.parse(jmlFile, subtree);
		} else
			return subtree.getNextSibling();
		//@ set parsed = true;
	}

	/**
	 * Links the statement.
	 * @return the link info resulting from the link
	 * @throws Jml2bException
	 **/
	/*@
	  @ requires parsed;
	  @*/
	LinkInfo linkStatement(IJml2bConfiguration config, LinkContext f)
		throws Jml2bException {
		exp.linkStatement(config, f);
		if (next != null)
			next.linkStatement(config, f);
		return null;
	}

	/**
	 * Collects all the indentifier of the list to give them an index in the 
	 * identifer array. This array is then analyzed to give short name when it
	 * is possible to identifiers.
	 * @see jml2b.pog.IdentifierResolver#bIdents
	 **/
	/*@
	  @ requires parsed;
	  @*/
	void processIdent() {
		exp.processIdent();
		if (next != null)
			next.processIdent();
	}

	/** 
	 * Replaces <code>this</code> with the parameter in the expressions.
	 * @param b expression on which the method where the expression occurs is 
	 * called.
	 * @return the modified list
	 **/
	/*@
	  @ requires parsed;
	  @*/
	ListExp instancie(Expression b) {
		exp = (Expression) exp.instancie(b);
		next = (next == null ? null : next.instancie(b));
		return this;
	}

	/**
	 * Returns the set of parsed items that correspond to those expressions
	 * @return the set of parsed item that correspond to the expressions 
	 * of the list 
	 **/
	/*@
	  @ requires parsed;
	  @*/
	public Vector getParsedItems() {
		Vector res = exp.getParsedItems();
		if (next != null)
			res.addAll(next.getParsedItems());
		return res;
	}

	public void setParsedItem(ParsedItem pi) {
		exp.setParsedItem(pi);
		if (next != null)
			next.setParsedItem(pi);
	}

	/**
	 * Returns the proof corresponding to the initialization of an array.
	 * @param config The current configuration
	 * @param field The formula corresponding to the created array
	 * @param fieldType The type of the created array
	 * @param length The temporary variable corresponding to the length of the 
	 * array
	 * @param normalBehaviour The current normal behaviour proof
	 * @param exceptionalBehaviour The current exceptional behaviour proofs
	 * stack
	 * @param indice The indice of the current element of the array
	 * @return The proof corresponding to the declaration of an array
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
		if (next != null)
			return exp.arrayDeclaration(
				config,
				field,
				fieldType,
				length,
				next.arrayDeclaration(
					config,
					field,
					fieldType,
					length,
					normalBehaviour,
					exceptionalBehaviour,
					indice + 1),
				exceptionalBehaviour,
				indice);
		else
			return exp.arrayDeclaration(
				config,
				field,
				fieldType,
				length,
				normalBehaviour,
				exceptionalBehaviour,
				indice);
	}

	static final long serialVersionUID = 3986804042295473223L;

	/**
	 * @return
	 */
	public Expression getExp() {
		return exp;
	}

	/**
	 * @return
	 */
	public ListExp getNext() {
		return next;
	}

}

/**
 * This class implements an array initializer statement, that is, for instance,  
 * <code>{ {"car", "house" }, {"dog", "cat", "monkey"} }</code>.
 * @author L. Burdy
 **/
public class ArrayInitializer extends Expression {

	/**
	 * The list of expressions. Those expression can be array initializer 
	 * themseleves when a multi-dimensionnal array is parsed. It can be
	 * <code>null</code> if the array has an empty initialization
	 **/
	private ListExp listExp;

	/**
	 * Constructs an expression as a <i>parsed item</i>.
	 * @param jf The file where the statement is located
	 * @param tree The <code>AST</code> node corresponding to the statement
	 * @see jml2b.structure.java.ParsedItem#ParsedItem(JmlFile, AST)
	 **/
	protected ArrayInitializer(JmlFile jf, AST tree) {
		super(jf, tree);
	}

	/**
	 * Constructs an array initializer from another one.
	 * @param l The expression list
	 **/
	private ArrayInitializer(ListExp l) {
		listExp = l;
		//@ set parsed = true;
	}

	/**
	 * Clones the array initializer
	 * @return hte cloned array initializer
	 **/
	public Object clone() {
		ArrayInitializer res =
			new ArrayInitializer(
				listExp == null ? null : (ListExp) listExp.clone());
		res.setBox(this);
		return res;
	}

	public boolean equals(Expression e) {
		return e instanceof ArrayInitializer
			&& listExp == null
				? ((ArrayInitializer) e).listExp == null
				: (((ArrayInitializer) e).listExp != null
					&& listExp.equals(((ArrayInitializer) e).listExp));
	}

	/**
	 * @throws InternalError since an array initializer appears only in 
	 * expression with side effects.
	 **/
	FormulaWithSpecMethodDecl exprToContextForm(
		IJml2bConfiguration config,
		Vector methods,
		boolean pred) {
		throw new jml2b.exceptions.InternalError(
			"Unreachable code reached : ArrayInitializer.exprToContextForm");
	}

	public AST parse(AST tree) throws Jml2bException {
		AST subtree = tree.getNextSibling();
		if (subtree.getType() == RCURLY)
			return subtree.getNextSibling();
		listExp = new ListExp();
		//@ set parsed = true;
		return listExp.parse(getJmlFile(), subtree);
	}

	/**
	 * @throws InternalError since an array initializer appears only in 
	 * expression with side effects.
	 **/
	public String toJava(int indent) {
		throw new jml2b.exceptions.InternalError(
			"Unreachable code reached : ArrayInitializer.exprToContextForm");
	}

	public LinkInfo linkStatement(IJml2bConfiguration config, LinkContext f)
		throws Jml2bException {
		if (listExp != null) {
			listExp.linkStatement(config, f);
		}
		return null;
	}

	public Type typeCheck(IJml2bConfiguration config, LinkContext f)
		throws Jml2bException {
		return null;
	}

	public void processIdent() {
		if (listExp != null)
			listExp.processIdent();
	}

	public Expression subField(Field f, Field newF) {
		return this;
	}

	public Expression subResult(String ww) {
		return this;
	}

	/**
	 * @throws InternalError since an array initializer appears only in 
	 * expression with side effects.
	 **/
	public void isModifiersCompatible(IJml2bConfiguration config, Modifiers modifiers) {
		throw new jml2b.exceptions.InternalError(
			"Unreachable code reached : ArrayInitializer.exprToContextForm");
	}

	public JmlExpression instancie(Expression b) {
		if (listExp != null)
			listExp = listExp.instancie(b);
		return this;
	}

	public JmlExpression instancie() {
		return this;
	}

	public boolean isConstant() {
		return false;
	}

	//	Vector getFreshVars() {
	//		return new Vector();
	//	}

	public Vector getParsedItems() {
		Vector res = new Vector();
		if (listExp != null)
			res = listExp.getParsedItems();
		res.add((ParsedItem) this);
		return res;
	}

	public void setParsedItem(ParsedItem pi) {
		if (listExp != null)
			listExp.setParsedItem(pi);
		change(pi);
	}

	/**
	 * @throws InternalError since an array initializer appears only in 
	 * expression with side effects.
	 **/
	public void old() {
		throw new jml2b.exceptions.InternalError(
			"Unreachable code reached : ArrayInitializer.exprToContextForm");
	}

	Proofs arrayDeclaration(
		IJml2bConfiguration config,
		Formula field,
		Type fieldType,
		String length,
		Proofs normalBehaviour,
		ExceptionalBehaviourStack exceptionalBehaviour,
		int indice)
		throws Jml2bException, PogException, LanguageException {
		ElementsForm elements =
			ElementsForm.getElementsName(fieldType.getElemType());

		String newField = freshObject();

		//		BinaryForm newElements =
		//			new BinaryForm(
		//				B_OVERRIDING,
		//				new TerminalForm(elements),
		//				new BinaryForm(
		//					B_COUPLE,
		//					field,
		//					new BinaryForm(
		//						B_OVERRIDING,
		//						new BinaryForm(
		//							IFormToken.B_APPLICATION,
		//							new TerminalForm(elements),
		//							field),
		//						new BinaryForm(
		//							B_COUPLE,
		//							new TerminalForm(indice),
		//							new TerminalForm(newField)))));
		// newElements = elements 
		//               <+ {field |-> elements(field) <+ {indice |-> newField}}

		Proofs p =
			arrayDeclaration(
				config,
				new TerminalForm(newField),
				fieldType.getElemType(),
				normalBehaviour.sub(
					new SubTmpVar(length, new TerminalForm(indice + 1))),
				exceptionalBehaviour).sub(
				new SubArrayElementSingle(
					elements,
					field,
					new TerminalForm(indice),
					new TerminalForm(newField)));

		p.addHyp(BinaryForm.getDefaultRefDecl(new TerminalForm(newField)));

		return p.quantify(newField, TerminalForm.$References);
	}

	/**
	 * Returns the proof corresponding to the declaration and the 
	 * initialization of an array.
	 * @param config The current configuration
	 * @param field The formula corresponding to the created array
	 * @param fieldType The type of the created array
	 * @param normalBehaviour The current normal behaviour proof
	 * @param exceptionalBehaviour The current exceptional behaviour proofs
	 * stack
	 * @return The proof corresponding to the declaration of an array
	 **/
	/*@
	  @ requires parsed;
	  @*/
	Proofs arrayDeclaration(
		IJml2bConfiguration config,
		Formula field,
		Type fieldType,
		Proofs normalBehaviour,
		ExceptionalBehaviourStack exceptionalBehaviour)
		throws Jml2bException, PogException, LanguageException {

		// Temporary variable representing the length of the array. It is used
		// to asign a value to arraylength, and it is calculated during the 
		// initializer evaluation.
		String length = fresh();

		BinaryForm newArraylength =
			new BinaryForm(
				B_OVERRIDING,
				TerminalForm.getArraylength(config),
				new BinaryForm(B_COUPLE, field, new TerminalForm(length)));
		// newArraylength = arraylength <+ {field |-> length}

		if (listExp == null) {
			// If there is no initializer, the length is initialized to 0,
			// typeof is overrided and a new element is added to the set of
			// instances.
			return normalBehaviour
				.sub(new SubArrayLength(newArraylength))
				.sub(
					new SubTypeofSingle(
						field,
						new TTypeForm(IFormToken.Jm_T_TYPE, fieldType)))
				.sub(new SubInstancesSingle(field))
				.sub(new SubTmpVar(length, new TerminalForm("0")));
		} else {
			//			String elements =
			//				ElementsForm
			//					.getElementsName(fieldType.getElemType())
			//					.toLang("B", 0)
			//					.toUniqString();

			//			BinaryForm newElements =
			//				new BinaryForm(
			//					B_OVERRIDING,
			//					ElementsForm.getElementsName(fieldType.getElemType()),
			//					new BinaryForm(
			//						B_COUPLE,
			//						field,
			//						new TerminalForm(B_EMPTYSET, "{}")));
			//			// newElements = elements <+ {field |-> {}}

			return listExp
				.arrayDeclaration(
					config,
					field,
					fieldType,
					length,
					normalBehaviour.sub(
						new SubArrayLength(newArraylength)).sub(
						new SubTypeofSingle(
							field,
							new TTypeForm(IFormToken.Jm_T_TYPE, fieldType))),
					exceptionalBehaviour,
					0)
				.sub(new SubInstancesSingle(field));
			//				.sub(new SubArrayElement(elements, newElements));
		}
	}

	/**
	 * @throws InternalError, the methods arrayDeclaration are used to 
	 * calculate the lemmas.
	 * @see ArrayInitializer#arrayDeclaration(IJml2bConfiguration, Formula, 
	 * Type, Proofs, ExceptionalBehaviourStack)
	 **/
	public Proofs wp(
		IJml2bConfiguration config,
		String result,
		Proofs normalBehaviour,
		ExceptionalBehaviourStack exceptionalBehaviour) {
		throw new jml2b.exceptions.InternalError(
			"Unreachable code reached : ArrayInitializer.wp");
	}

	static final long serialVersionUID = 1890926686273759548L;

	public void getPrecondition(
		IJml2bConfiguration config,
		ModifiableSet modifies,
		Vector req,
		Vector ens)
		throws Jml2bException, PogException {
		ListExp le = listExp;
		while (le != null) {
			le.getExp().getPrecondition(config, modifies, req, ens);
			//			modifies.add(le.getExp().getModifies());
			le = le.getNext();
		}
	}

	public void collectCalledMethod(Vector calledMethod) {
		ListExp le = listExp;
		while (le != null) {
			le.getExp().collectCalledMethod(calledMethod);
			le = le.getNext();
		}
	}

	void getFreeVariable(Set s) {
	}

}