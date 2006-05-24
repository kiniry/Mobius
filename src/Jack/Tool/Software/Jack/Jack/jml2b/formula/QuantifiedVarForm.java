//******************************************************************************
/* Copyright (c) 2002, 2003 GEMPLUS Software Research Labs. All Rights Reserved.
/* Copyright (c) 2003, 2004 INRIA. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: QuantifiedVarForm.java
/*
/*******************************************************************************
/* Warnings/Remarks:
/*  09/26/2003 : Simplify integration achieved
/******************************************************************************/
package jml2b.formula;

import java.io.IOException;

import jml2b.IJml2bConfiguration;
import jml2b.exceptions.LanguageException;
import jml2b.exceptions.LoadException;
import jml2b.languages.ITranslationResult;
import jml2b.languages.Languages;
import jml2b.structure.java.IJmlFile;
import jml2b.util.IOutputStream;
import jml2b.util.JpoInputStream;
import jml2b.util.Profiler;

/**
 * This class implements a list of quatified variables.
 * @author L. Burdy
 */
public class QuantifiedVarForm extends Profiler {

	/**
	 * The name of the current variable
	 **/
	protected TerminalForm var;

	/**
	 * The type of the current variable
	 **/
	protected Formula type;

	/**
	 * The next element in the list.
	 **/
	protected QuantifiedVarForm next;

	/*@
	  @ private invariant var != null;
	  @                && type != null;
	  @*/

	public QuantifiedVarForm(QuantifiedVarForm qvf) {
		var = qvf.var;
		type = qvf.type;
		next = qvf.next;
	}

	/**
	 * Creates an empty list will be completed when performing the load.
	 * @param s input stream corresponding to a jpo file. 
	 * @throws IOException if the end of the stream is reached before the 
	 * formula has been read
	 * @throws LoadException if the stream has not a good format.
	 **/
	/*@
	  @ requires s != null;
	  @*/
	QuantifiedVarForm(
		IJml2bConfiguration config,
		IJmlFile fi,
		JpoInputStream s)
		throws IOException, LoadException {
		var = (TerminalForm) Formula.create(config, s, fi);
		type = Formula.create(config, s, fi);
		if (s.readBoolean()) {
			next = new QuantifiedVarForm(config, fi, s);
		}
	}

	/**
	 * Creates a list with one quantified variable.
	 * @param var The variable name.
	 * @param type The variable type.
	 **/
	/*@
	  @ requires var != null && type != null;
	  @*/
	public QuantifiedVarForm(TerminalForm var, Formula type) {
		this(var, type, null);
	}

	/**
	 * Creates a quantified variable list from another one.
	 * @param var The current variable name
	 * @param type The current variable type
	 * @param next The next element of the list
	 **/
	/*@
	  @ requires var != null && type != null;
	  @*/
	public QuantifiedVarForm(
		TerminalForm var,
		Formula type,
		QuantifiedVarForm next) {
		this.var = var;
		this.type = type;
		this.next = next;
	}

	/**
	 * Clones the quantified variables
	 **/
	public Object clone() {
		return new QuantifiedVarForm(
			var,
			(Formula) type.clone(),
			next == null ? null : (QuantifiedVarForm) next.clone());
	}

	/**
	 * Saves the quantified variables into an output stream.
	 * @param s the ouputstream corresponding to a jpo file
	 * @throws IOException when the formula cannot be saved.
	 **/
	/*@
	  @ requires s != null;
	  @*/
	void save(IJml2bConfiguration config, IOutputStream s, IJmlFile jf) throws IOException {
		var.save(config, s, jf);
		type.save(config, s, jf);
		if (next == null)
			s.writeBoolean(false);
		else {
			s.writeBoolean(true);
			next.save(config, s, jf);
		}
	}

	/**
	 * Collects all the indentifier of the quantified variables to give them an 
	 * index in the identifer array. This array is then analyzed to give short 
	 * name when it is possible to identifiers.
	 * @see jml2b.pog.IdentifierResolver#bIdents
	 **/
	void processIdent() {
		var.processIdent();
		if (next != null)
			next.processIdent();
	}

	/**
	 * Tests whether a string belongs to the current quantified variables.
	 * @param a The tested string
	 * @return <code>true</code> if a quantified variable equals <code>a</code>, 
	 * <code>false</code> otherwise
	 **/
	/*@
	  @ requires a != null;
	  @*/
	boolean contain(String a) {
		if (a.equals(var.getNonAmbiguousName()))
			return true;
		else if (next != null)
			return next.contain(a);
		else
			return false;
	}

	/**
	 * Tests whether a formula belongs to the current quantified variables.
	 * @param a The tested formula
	 * @return <code>true</code> if a quantified variable equals <code>a</code>, 
	 * <code>false</code> otherwise
	 **/
	/*@
	  @ requires a != null;
	  @*/
	boolean contain(Formula a) {
		if (a.equals(var))
			return true;
		else if (next != null)
			return next.contain(a);
		else
			return false;
	}

	/**
	 * Applies a substitution on quantified variables.
	 * @param a the substituted formula
	 * @param b the new formula
	 * @param subInCalledOld specify whether the substitution should also be 
	 * applied in the <i>called old</i> construction
	 * @return the quantified variables where the substitution has been applied.
	 **/
	QuantifiedVarForm sub(Formula a, Formula b, boolean subInCalledOld) {
		Formula tmptype = type.sub(a, b, subInCalledOld);
		QuantifiedVarForm tmpnext =
			next == null ? null : next.sub(a, b, subInCalledOld);
		if (tmptype == type && tmpnext == next)
			return this;
		else
			return new QuantifiedVarForm(var, tmptype, tmpnext);
	}

	/**
	 * Applies a substitution on quantified variables.
	 * @param a the substituted string correspondingto an identifier
	 * @param b the new formula
	 * @return the quantified variables where the substitution has been applied.
	 **/
	QuantifiedVarForm subIdent(String a, Formula b) {
		Formula tmptype = type.subIdent(a, b);
		QuantifiedVarForm tmpnext = next == null ? null : next.subIdent(a, b);
		if (tmptype == type && tmpnext == next)
			return this;
		else
			return new QuantifiedVarForm(var, tmptype, tmpnext);
	}

	/**
	 * Returns whether the quantified variables are equal to the parameter.
	 * @param f the checked parameter
	 * @return <code>true</code> if the quantified variables syntaxically equal 
	 * the parameter, <code>false</code> otherwise
	 **/
	/*@
	  @ requires f != null;
	  @*/
	boolean equals(QuantifiedVarForm f) {
		return var.equals(f.var)
			&& type.equals(f.type)
			&& ((next == null && f.next == null) || next.equals(f.next));
	}

	/**
	 * Returns whether the quantified variables corresponds to read quantified 
	 * variables.
	 * @param f read quantified variables coming from a jpo file
	 * @return <code>true</code> if the quantified variables equal to read 
	 * quantified variable, <code>false</code> otherwise.
	 * @throws MergeException
	 **/
	/*@
	  @ requires f != null;
	  @*/
	boolean is(QuantifiedVarForm f) {
		return var.is(f.var)
			&& type.is(f.type)
			&& ((next == null && f.next == null)
				|| (next != null && f.next != null && next.is(f.next)));
	}

	/**
	 * Annotates all the fields that appear in the quantified variables in order 
	 * to declare them in the Atelier B files.
	 **/
	void garbageIdent() {
		var.garbageIdent();
		if (next != null)
			next.garbageIdent();
	}

	public ITranslationResult toLang(String language, int indent)
		throws LanguageException {
		return Languages.getLanguageClass(language).quantifiedVarFactory(
			this).toLang(
			indent);
	}

	/**
	 * @return
	 */
	public QuantifiedVarForm getNext() {
		return next;
	}

	/**
	 * @return
	 */
	public Formula getType() {
		return type;
	}

	/**
	 * @return
	 */
	public TerminalForm getVar() {
		return var;
	}

}
