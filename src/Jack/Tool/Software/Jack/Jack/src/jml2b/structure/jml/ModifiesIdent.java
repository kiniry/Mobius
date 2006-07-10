//******************************************************************************
/* Copyright (c) 2002, 2003 GEMPLUS Software Research Labs. All Rights Reserved.
/* Copyright (c) 2003, 2004 INRIA. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: ModifiesIdent.java
/*
/*******************************************************************************
/* Warnings/Remarks:
/*  09/26/2003 : Simplify integration achieved
/******************************************************************************/
package jml2b.structure.jml;

import java.util.Vector;

import jml2b.IJml2bConfiguration;
import jml2b.exceptions.Jml2bException;
import jml2b.exceptions.LinkException;
import jml2b.formula.BinaryForm;
import jml2b.formula.Formula;
import jml2b.formula.IFormToken;
import jml2b.formula.IModifiesField;
import jml2b.formula.ModifiedFieldForm;
import jml2b.formula.TTypeForm;
import jml2b.formula.TerminalForm;
import jml2b.formula.UnaryForm;
import jml2b.link.LinkContext;
import jml2b.link.LinkInfo;
import jml2b.pog.lemma.FormulaWithSpecMethodDecl;
import jml2b.pog.lemma.Proofs;
import jml2b.pog.substitution.SubForm;
import jml2b.pog.util.IdentifierResolver;
import jml2b.structure.AField;
import jml2b.structure.java.Field;
import jml2b.structure.java.Identifier;
import jml2b.structure.java.JmlFile;
import jml2b.structure.java.ParsedItem;
import jml2b.structure.java.Type;
import jml2b.structure.statement.Expression;
import jml2b.structure.statement.TerminalExp;
import antlr.collections.AST;

/**
 * This class corresponds to a modified field. This field can be static or 
 * member if it comes from a <i>depends</i> clause.
 * @author L. Burdy
 **/
public class ModifiesIdent extends Modifies {

	/**
	 * The modified field
	 **/
	private Identifier ident;

	/*@
	  @ private invariant ident != null;
	  @*/

	/**
	 * Constructs a modified variable corresponding to a parsed item.
	 * @param jf The current JML file
	 * @param a The tree corresponding to this modifies
	 **/
	ModifiesIdent(JmlFile jf, AST tree) {
		super(jf, tree);
		ident = new Identifier(tree.getText());
	}

	/**
	 * Constructs a modified identifier from an identifier.
	 * @param pi The parsed item
	 * @param t The type of the parsed item
	 * @param ident The identifier
	 **/
	/*@
	  @ requires ident != null;
	  @*/
	public ModifiesIdent(ParsedItem pi, Type t, Identifier ident) {
		super(pi, t);
		this.ident = ident;
	}

	/**
	 * Constructs a modifies corresponding to an identifier
	 * @param pi The parsed item associated with this modified identifier
	 * @param i The modified identifier
	 **/
	/*@
	  @ requires i != null;
	  @*/
	public ModifiesIdent(AField f, Identifier i) {
		super(f, f.getType());
		ident = i;
	}

	public Object clone() {
		return new ModifiesIdent(this, getStateType(), ident);
	}

	Vector getParsedItems() {
		Vector res = new Vector();
		res.add((ParsedItem) this);
		return res;
	}

	void setParsedItem(ParsedItem pi) {
		change(pi);
	}

	/**
	 * @return <code>ident</code>
	 **/
	FormulaWithSpecMethodDecl getFormula(IJml2bConfiguration config) {
		return new FormulaWithSpecMethodDecl(new TerminalForm(ident));
	}

	/**
	 * @return <code>{ident}</code>
	 **/
	FormulaWithSpecMethodDecl getSet(IJml2bConfiguration config) {
		FormulaWithSpecMethodDecl fwp = getFormula(config);
		return new FormulaWithSpecMethodDecl(fwp, new UnaryForm(B_ACCOLADE, fwp.getFormula()));
	}

	/**
	 * @return <code>ident</code>
	 **/
	String toJava(int indent) {
		if (ident.field != null
			&& ident.field.getModifiers() != null
			&& ident.field.getModifiers().isStatic())
			return ident.field.getDefiningClass().getName()
				+ "."
				+ ident.getName();
		else
			return ident.getName();
	}

	/**
	 * @throws LinkException when the modified identifier is not linked as a 
	 * field.
	 **/
	LinkInfo linkStatements(IJml2bConfiguration config, LinkContext f)
		throws Jml2bException {
		LinkInfo res = ident.linkFieldIdent(config, f, this);
		setStateType(res.getType());
		if (ident.idType != Identifier.ID_FIELD)
			throw new LinkException(
				"identifier "
					+ ident.getName()
					+ " should correspond to a field",
				this);
		return res;
	}

	public Type typeCheck(IJml2bConfiguration config, LinkContext f) {
		return null;
	}

	Modifies instancie() {
		if (ident.field.isLocal()
			|| ident.field.getModifiers().isStatic())
			return this;
		else
			return new ModifiesDot(
				this,
				getStateType(),
				new TerminalExp(LITERAL_this, "this"),
				this);
	}

	void instancie(Expression b) {
	}

	/**
	 * If the type of the field is builtin, returns
	 * <code>\forall type newName; [ident := newName]s</code> else returns
	 * <code>\forall REFERENCES newName; newName != null && 
	 *                                   \typeof(NewName) <: type ==> s</code>
	 **/
	Proofs applyMod(IJml2bConfiguration config, IModifiesField m, Proofs s) {
		ModifiedFieldForm mff = new ModifiedFieldForm(ident.field, m);
		Proofs res = s.sub(new SubForm(new TerminalForm(ident), mff));
		if (ident.field.getType().isBuiltin())
			return res.quantify(
				mff,
				new TTypeForm(IFormToken.T_TYPE, ident.field.getType()));
		else {
			res.addHyp(
				new BinaryForm(
					Jm_IMPLICATION_OP,
					new BinaryForm(
						Ja_DIFFERENT_OP,
						mff,
						new TerminalForm(Ja_LITERAL_null, "null")),
					new BinaryForm(
						Jm_IS_SUBTYPE,
						new BinaryForm(B_APPLICATION, TerminalForm.$typeof, mff),
						new TTypeForm(
							IFormToken.Jm_T_TYPE,
							ident.field.getType()))));
			return res.quantify(mff, TerminalForm.$References);
		}
	}

	/**
	 * @return <code>true</code> if <code>ident</code> corresponds the field, 
	 * <code>false</code> otherwise
	 **/
	boolean is(AField f) {
		return ident.field == f;
	}

	/**
	 * Applies no restriction to a static member field nor to local fields, 
	 * if it is member, restricts to its domain.
	 **/
	FormulaWithSpecMethodDecl getModifiedInstances(IJml2bConfiguration config, AField f) {
		if (ident.field.getModifiers() == null
			|| ident.field.getModifiers().isStatic())
			return null;
		else
			return new FormulaWithSpecMethodDecl(new UnaryForm(B_DOM, new TerminalForm(ident)));
	}

	/**
	 * Apply no restriction to the domain of the <code>xxxelements(f)</code> 
	 * function.
	 * @return <code>null</code>
	 **/
	FormulaWithSpecMethodDecl getModifiedIndexes(
		IJml2bConfiguration config,
		int tag,
		Formula q) {
		return null;
	}

	/**
	 * Apply no restriction to <code>xxxelements</code> variable.
	 * @return <code>null</code>
	 **/
	FormulaWithSpecMethodDecl restrictElement(IJml2bConfiguration config, int tag) {
		return null;
	}

	/**
	 * If the depends store ref is the same field, its dependees are added.
	 * Otherwise no store ref are added.
	 **/
	Vector addDepends(IJml2bConfiguration config, Depends d) {
		Modifies m = d.getAbstractField();
		if (m instanceof ModifiesIdent) {
			if (((ModifiesIdent) m).ident.equals(ident))
				return d.getConcreteFields();
		} else if (m instanceof ModifiesDot) {
			if (m.is(ident.field))
				return d.getConcreteFields();
		}
		return new Vector();
	}

	Modifies sub(IJml2bConfiguration config, Field a, Field b) {
		if (is(a)) {
			return new ModifiesIdent(this, getStateType(), new Identifier(b));
		} else
			return new ModifiesIdent(this, getStateType(), ident);
	}

	/**
	 * Sets a name index to the field.
	 **/
	void processIdent() {
		ident.field.nameIndex = IdentifierResolver.addIdent(ident.field);
	}

	/**
	 * Returns the identidentifer.
	 * @return <code>ident</code>
	 */
	public Identifier getIdent() {
		return ident;
	}

	/**
	 * Returns the field.
	 * @return <code>ident.field</code>
	 */
	public AField getField() {
		return ident.field;
	}

	/**
	 * @throws InternalError
	 **/
	Expression getInstanciation() {
		throw new InternalError("ModifiesIdent.getInstanciation");
	}

	/**
	 * Returns whether the field is member or not
	 * @return <code>true</code> if the field is not static, 
	 * <code>false</code> otherwise.
	 **/
	boolean isMemberNonInstanciated() {
		return !ident.field.getModifiers().isStatic();
	}

	static final long serialVersionUID = -4877642697340175328L;

	/* (non-Javadoc)
	 * @see jml2b.structure.jml.Modifies#equals(jml2b.structure.jml.Modifies)
	 */
	public boolean equals(IJml2bConfiguration config, Modifies m) {
		return m instanceof ModifiesIdent
		&& ((ModifiesIdent) m).ident.equals(ident);
	}

}
