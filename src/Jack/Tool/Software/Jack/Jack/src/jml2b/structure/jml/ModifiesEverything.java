//******************************************************************************
/* Copyright (c) 2002, 2003 GEMPLUS Software Research Labs. All Rights Reserved.
/* Copyright (c) 2003, 2004 INRIA. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: ModifiesEverything
/*
/*******************************************************************************
/* Warnings/Remarks:
/******************************************************************************/
package jml2b.structure.jml;

import java.util.HashSet;
import java.util.Iterator;
import java.util.Set;
import java.util.Vector;

import jml2b.IJml2bConfiguration;
import jml2b.exceptions.Jml2bException;
import jml2b.formula.BinaryForm;
import jml2b.formula.ElementsForm;
import jml2b.formula.Formula;
import jml2b.formula.IFormToken;
import jml2b.formula.IModifiesField;
import jml2b.formula.ModifiedFieldForm;
import jml2b.formula.TTypeForm;
import jml2b.formula.TerminalForm;
import jml2b.link.LinkContext;
import jml2b.link.LinkInfo;
import jml2b.pog.lemma.Proofs;
import jml2b.pog.lemma.SimpleLemma;
import jml2b.pog.substitution.SubForm;
import jml2b.pog.util.ColoredInfo;
import jml2b.structure.AField;
import jml2b.structure.java.Class;
import jml2b.structure.java.Identifier;
import jml2b.structure.java.JmlFile;
import jml2b.structure.java.Parameters;
import jml2b.structure.java.ParsedItem;
import jml2b.structure.java.Type;
import jml2b.structure.statement.Expression;
import antlr.collections.AST;

/**
 * This class implements a <code>\everything</code>
 * @author L. Burdy
 **/
public class ModifiesEverything extends ModifiesClause {

	/**
	 * Constructs an empty modifies clause.
	 **/
	public ModifiesEverything() {
	}

	/**
	 * Constructs an empty modifies clause corresponding to a parsed item.
	 * @param jf The current JML file
	 * @param a The tree corresponding to this modifies
	 **/
	ModifiesEverything(JmlFile jf, AST a) throws Jml2bException {
		super(jf, a);
	}

	public Object clone() {
		return this;
	}

	public void instancie(IJml2bConfiguration config) {
	}

	public void instancie(Expression b, IJml2bConfiguration config) {
	}

	public LinkInfo linkStatements(IJml2bConfiguration config, LinkContext f)
		throws Jml2bException {
		return null;
	}

	public Type typeCheck(IJml2bConfiguration config, LinkContext f)
		throws Jml2bException {
		return null;
	}

	public void processIdent() {
	}

	/**
	 * @return <code>\everything</code>
	 **/
	public String toJava(int indent) {
		return "\\everything";
	}

	/**
	 * @return an empty lemma
	 **/
	public SimpleLemma modifiesLemmas(
		IJml2bConfiguration config,
		Vector fields,
		Vector nonModifiedFields,
		Formula[] nonModifiedxxxElements) {
		return new SimpleLemma();
	}

	/**
	 * @return <code>this</code>
	 **/
	public ModifiesClause renameParam(
		IJml2bConfiguration config,
		Parameters signature,
		Vector newSignature) {
		return this;
	}

	/**
	 * Performs no action
	 **/
	public void addDepends(IJml2bConfiguration config, Class c) {
	}

	public Proofs modifies(
		IJml2bConfiguration config,
		IModifiesField m,
		Proofs s) {
		Set fields = new HashSet();

		// Collect the fields present in the current proof
		s.getFields(fields);

		// loop on collected fields
		Iterator i = fields.iterator();
		while (i.hasNext()) {
			AField f = (AField) i.next();
			ModifiedFieldForm mff = new ModifiedFieldForm(f, m);
			s = s.sub(new SubForm(new TerminalForm(new Identifier(f)), mff));
			if (f.getType().isBuiltin())
				s = s.quantify(mff, new TTypeForm(IFormToken.T_TYPE, f.getType()));
			else if (f.getModifiers().isStatic()){
				s.addHyp(
					new BinaryForm(
						Jm_IMPLICATION_OP,
						new BinaryForm(
							Ja_DIFFERENT_OP,
							mff,
							new TerminalForm(Ja_LITERAL_null, "null")),
						new BinaryForm(
							Jm_IS_SUBTYPE,
							new BinaryForm(
								B_APPLICATION,
								TerminalForm.$typeof,
								mff),
							new TTypeForm(IFormToken.Jm_T_TYPE, f.getType()))));
				s = s.quantify(mff, TerminalForm.$References);
			}
			else {
				s = s.quantify(
									mff,
									new BinaryForm(
										IS_MEMBER_FIELD,
										new TTypeForm(
											IFormToken.T_TYPE,
											new Type(f.getDefiningClass())),
										new TTypeForm(
											IFormToken.T_TYPE,
											f.getType())));

			}
		}

		// Loop on the xxxelements variable
		for (int j = 0; j < ElementsForm.elements.length; j++) {
			jml2b.formula.ElementsForm elements = ElementsForm.elements[j];
			TerminalForm newName = new ElementsForm(elements);

			s = s.sub(new SubForm(elements, newName));
			s = s.quantify(newName, elements.getType(), new ColoredInfo());
		}
		return s;
	}

	/**
	 * @return <code>this</code>
	 **/
	public ModifiesClause completeModifiesWithFields(ModifiesList l) {
		return this;
	}

	public void setParsedItem(ParsedItem pi) {
		change(pi);
	}

	static final long serialVersionUID = 6457218174405239122L;

}
