//******************************************************************************
/* Copyright (c) 2002, 2003 GEMPLUS Software Research Labs. All Rights Reserved.
/* Copyright (c) 2003, 2004 INRIA. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: ModifiesList.java
/*
/*******************************************************************************
/* Warnings/Remarks:
/*  09/26/2003 : Simplify integration achieved
/******************************************************************************/
package jml2b.structure.jml;

import java.util.Collection;
import java.util.Enumeration;
import java.util.Iterator;
import java.util.Vector;

import jml.JmlDeclParserTokenTypes;
import jml2b.IJml2bConfiguration;
import jml2b.exceptions.Jml2bException;
import jml2b.exceptions.PogException;
import jml2b.link.LinkContext;
import jml2b.link.LinkInfo;
import jml2b.pog.util.TemporaryField;
import jml2b.structure.java.Class;
import jml2b.structure.java.Field;
import jml2b.structure.java.Identifier;
import jml2b.structure.java.JavaLoader;
import jml2b.structure.java.JmlFile;
import jml2b.structure.java.Modifiers;
import jml2b.structure.java.Parameters;
import jml2b.structure.java.ParsedItem;
import jml2b.structure.java.Type;
import jml2b.structure.statement.Expression;
import antlr.collections.AST;

/**
 * This class describes the modifies clause as a list of {@link Modifies} 
 * elements.     
 * @author L. Burdy
 **/
public class ModifiesList
	extends ModifiesClause
	implements JmlDeclParserTokenTypes {

	/**
	 * The current modified variable
	 **/
	private GuardedModifies gm;

	/*@
	  @ private invariant gm != null;
	  @*/

	/**
	 * The next modified variable of the modifies list.
	 **/
	private ModifiesList next;

	/**
	 * Constructs an empty modified list corresponding to a parsed item.
	 * @param jf The current JML file
	 * @param a The tree corresponding to this modifies
	 **/
	ModifiesList(JmlFile jf, AST a) throws Jml2bException {
		super(jf, a);
		switch (a.getType()) {
			case COMMA :
				gm =
					new GuardedModifies(jf, a.getFirstChild().getNextSibling());
				next =
					(ModifiesList) ModifiesClause.create(jf, a.getFirstChild());
				break;
			default :
				gm = new GuardedModifies(jf, a);
				next = null;
		}
	}

	/**
	 * Constructs a list from a new {@link Modifies} element and a list.
	 * @param m The modified variable
	 * @param ml The list
	 **/
	/*@
	  @ requires m != null;
	  @*/
	public ModifiesList(GuardedModifies m, ModifiesList ml) {
		super(m);
		gm = m;
		next = ml;
	}

	/**
	 * @param fields
	 */
	/*@
	  @ requires fields != null && fields.elementType <: \type(Fields);
	  @*/
	public ModifiesList(Enumeration fields) {
		Field f = (Field) fields.nextElement();
		ModifiesList tmp = null;
		if (fields.hasMoreElements()) {
			tmp = new ModifiesList(fields);
		}
		gm = new GuardedModifies(f, new Identifier(f));
		if (f.getType().isArray()) {
			next = new ModifiesList(new GuardedModifies(f), tmp);
		} else
			next = tmp;
	}

	public ModifiesList(Iterator fields) {
		Field f = (Field) fields.next();
		ModifiesList tmp = null;
		if (fields.hasNext()) {
			tmp = new ModifiesList(fields);
		}
		gm = new GuardedModifies(new Identifier(f), f);
		if (f.getType().isArray()) {
			next = new ModifiesList(new GuardedModifies(f), tmp);
		} else
			next = tmp;
	}

	/**
	 * Clones the list.
	 * @return the cloned list
	 **/
	public Object clone() {
		return new ModifiesList(
			(GuardedModifies) gm.clone(),
			next == null ? null : (ModifiesList) next.clone());
	}

		/**
	 * Concats two lists.
	 * @param ml The list to concat to the current one
	 **/
	public void add(ModifiesList ml) {
		while (ml != null) {
			addModifies(ml.gm);
			ml = ml.next;
		}
	}

	public boolean addWithoutDoublon(
		IJml2bConfiguration config,
		ModifiesList ml) {
		boolean res = false;
		while (ml != null) {
			res = addModifiesWithoutDoublon(config, ml.gm) || res;
			ml = ml.next;
		}
		return res;
	}

	/**
	 * Adds a new {@link GuardedModifies} element at the head of the list.
	 * @param gm The added element
	 **/
	void addModifies(GuardedModifies gm) {
		if (next == null)
			next = new ModifiesList(gm, null);
		else
			next.addModifies(gm);
	}

	public boolean addModifiesWithoutDoublon(
		IJml2bConfiguration config,
		GuardedModifies gm) {
		ModifiesList tmp = this;
		while (tmp != null) {
			if (tmp.gm.equals(config, gm))
				return false;
			tmp = tmp.next;
		}
		addModifies(gm);
		return true;
	}

	public LinkInfo linkStatements(IJml2bConfiguration config, LinkContext f)
		throws Jml2bException {
		LinkInfo l = gm.linkStatements(config, f);
		if (next != null) {
			next.linkStatements(config, f);
			return null;
		} else
			return l;
	}

	public Type typeCheck(IJml2bConfiguration config, LinkContext f)
		throws Jml2bException {
		gm.typeCheck(config, f);
		if (next != null)
			next.typeCheck(config, f);
		return null;
	}



	/**
	 * Renames the parameter in the list.
	 * @param signature the signature of the called method
	 * @param newSignature the list of new names
	 * @return the current <list renamed
	 * @throws PogException
	 * @see Proofs#renameParam(Parameters, Vector)
	 **/
	private ModifiesList renameParam(
		IJml2bConfiguration config,
		Enumeration signature,
		Enumeration newSignature)
		throws PogException {
		if (signature.hasMoreElements()) {
			Field f = (Field) signature.nextElement();
			Field newF;
			Object o = newSignature.nextElement();
			if (o instanceof Field)
				newF = (Field) o;
			else
				newF =
					new TemporaryField(
						f,
						(Modifiers) f.getModifiers(),
						f.getType(),
						(String) o,
						f.getAssign());
			return renameParam(config, signature, newSignature).sub(
				config,
				f,
				newF);
		} else
			return this;
	}

	public ModifiesClause renameParam(
		IJml2bConfiguration config,
		Parameters signature,
		Vector newSignature)
		throws PogException {
		return renameParam(
			config,
			signature.signature.elements(),
			newSignature.elements());
	}

	public void instancie(IJml2bConfiguration config) throws PogException {
		gm = gm.instancie(config);
		if (next != null)
			next.instancie(config);
	}

	/*@
	  @ requires gm instanceof NormalizedGuardedModifies;
	  @*/
	public void instancie(Expression b, IJml2bConfiguration config)
		throws PogException {
		((NormalizedGuardedModifies) gm).instancie(config, b);
		if (next != null)
			next.instancie(b, config);
	}

	/**
	 * Substitutes two fields in the list.
	 * @param a The field to substitute
	 * @param b The new field
	 * @return The substituted list
	 * @throws PogException
	 **/
	/*@
	  @ requires gm instanceof NormalizedGuardedModifies;
	  @*/
	private ModifiesList sub(IJml2bConfiguration config, Field a, Field b)
		throws PogException {
		ModifiesList res = (ModifiesList) clone();
		if (gm instanceof NormalizedGuardedModifies)
			res.gm = ((NormalizedGuardedModifies) gm).sub(config, a, b);
		else
			res.gm = gm.subField(config, a, b);
		res.next = next == null ? null : next.sub(config, a, b);
		return res;
	}

	public void processIdent() {
		gm.processIdent();
		if (next != null)
			next.processIdent();
	}

			/**
	 * Complete the modifies with modified store-ref issued from a depends 
	 * clause.
	 * @param d The depends clause
	 **/
	private void addDepends(IJml2bConfiguration config, Depends d)
		throws PogException {
		add(((NormalizedGuardedModifies) gm).addDepends(config, d));
		if (next != null) {
			next.addDepends(config, d);
		}
	}

	public void addDepends(IJml2bConfiguration config, Class c)
		throws PogException {
		Enumeration a = c.getAccessibleDepends((JavaLoader) config.getPackage());
		while (a.hasMoreElements()) {
			Depends d = (Depends) a.nextElement();
			addDepends(config, d);
		}
	}

	public ModifiesClause completeModifiesWithFields(ModifiesList l) {
		add(l);
		return this;
	}

	public void setParsedItem(ParsedItem pi) {
		gm.setParsedItem(pi);
		if (next != null)
			next.setParsedItem(pi);
	}

	public Collection getFields() {
		Collection res = gm.getFields();
		if (next != null)
			res.addAll(next.getFields());
		return res;
	}

	static final long serialVersionUID = -2459907009180805970L;
	/**
	 * @return
	 */
	public GuardedModifies getGm() {
		return gm;
	}

	/**
	 * @return
	 */
	public ModifiesList getNext() {
		return next;
	}

}
