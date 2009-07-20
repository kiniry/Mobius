//******************************************************************************
/* Copyright (c) 2002, 2003 GEMPLUS Software Research Labs. All Rights Reserved.
/* Copyright (c) 2003, 2004 INRIA. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: QuantifiedForm.java
/*
/*******************************************************************************
/* Warnings/Remarks:
/*  09/26/2003 : Simplify integration achieved
/******************************************************************************/
package jml2b.formula;

import java.io.IOException;
import java.util.Set;
import java.util.Vector;

import jml2b.IJml2bConfiguration;
import jml2b.exceptions.LoadException;
import jml2b.structure.java.IJmlFile;
import jml2b.util.IOutputStream;
import jml2b.util.JpoInputStream;

/**
 * This class implements quantified formula: universal, existential or union.
 * The token associated with those formulas can be 
 * <UL>
 * <li> <code>Jm_FORALL</code>
 * <li> <code>Jm_EXISTS</code>
 * </UL>
 * @author L. Burdy
 */
public class QuantifiedForm extends Formula {

	/**
	 * The set of quantified variables
	 **/
	protected QuantifiedVarForm vars;

	/**
	 * The quantified formula
	 **/
	protected Formula body;

	/*@
	  @ private invariant vars != null;
	  @                && body != null;
	  @*/

	/**
	 * Constructs a quantified formula from a loaded 
	 * <a href="{@docRoot}/jpov/doc-files/jpo.html"> .jpo file</a>.
	 * @param config The current configuration
	 * @param nodeType token of the new formula
	 * @param s input stream corresponding to a jpo file. 
	 * @throws IOException if the end of the stream is reached before the 
	 * formula has been read
	 * @throws LoadException if the stream has not a good format.
	 **/
	/*@ 
	  @ requires s != null;
	  @*/
	QuantifiedForm(
		IJml2bConfiguration config,
		IJmlFile fi,
		byte nodeType,
		JpoInputStream s)
		throws IOException, LoadException {
		super(nodeType);
		vars = new QuantifiedVarForm(config, fi, s);
		body = Formula.create(config, s, fi);
	}

	public QuantifiedForm(QuantifiedForm f) {
		super(f.getNodeType());
		this.vars = f.vars;
		this.body = f.body;
	}

	/**
	 * Constructs a quantified formula from a set of variables and a formula.
	 * @param nodeType token of the new formula
	 * @param vars The set of quantified variables
	 * @param body The quantified formula
	 **/
	/*@
	  @ requires vars != null;
	  @ requires body != null;
	  @*/
	public QuantifiedForm(
		byte nodeType,
		QuantifiedVarForm vars,
		Formula body) {
		super(nodeType);
		this.vars = vars;
		this.body = body;
	}

	public Object clone() {
		QuantifiedForm res =
			new QuantifiedForm(
				getNodeType(),
				(QuantifiedVarForm) vars.clone(),
				(Formula) body.clone());
		return res;
	}

	public void processIdent() {
		vars.processIdent();
		body.processIdent();
	}

	public Formula instancie(Formula b) {
		body = body.instancie(b);
		return this;
	}

	public Formula sub(Formula a, Formula b, boolean subInCalledOld) {
		if (!(a.getNodeType() == Ja_IDENT && vars.contain(a))) {
			QuantifiedVarForm tmpvars = vars.sub(a, b, subInCalledOld);
			Formula tmpbody = body.sub(a, b, subInCalledOld);
			if (tmpvars == vars && tmpbody == body)
				return this;
			else
				return new QuantifiedForm(getNodeType(), tmpvars, tmpbody);
		} else
			return this;
	}

	public Formula suppressSpecialOld(int token) {
		Formula tmpbody = body.suppressSpecialOld(token);
		if (tmpbody == body)
			return this;
		else
			return new QuantifiedForm(getNodeType(), vars, tmpbody);
	}

	public Formula subIdent(String a, Formula b) {
		if (!vars.contain(a)) {
			QuantifiedVarForm tmpvars = vars.subIdent(a, b);
			Formula tmpbody = body.subIdent(a, b);
			if (tmpvars == vars && tmpbody == body)
				return this;
			else
				return new QuantifiedForm(getNodeType(), tmpvars, tmpbody);
		} else
			return this;
	}

	public boolean equals(Object f) {
		return getNodeType() == ((Formula) f).getNodeType()
			&& vars.equals(((QuantifiedForm) f).vars)
			&& body.equals(((QuantifiedForm) f).body);
	}

	/*@
	  @ requires f != null;
	  @*/
	public boolean is(Formula f) {
		return getNodeType() == f.getNodeType()
			&& vars.is(((QuantifiedForm) f).vars)
			&& body.is(((QuantifiedForm) f).body);
	}

	public int contains(Vector selectedFields) {
		return body.contains(selectedFields);
	}
	
	public boolean isObvious(boolean atTheEnd) {
		return false;
	}

	public void save(IJml2bConfiguration config, IOutputStream s, IJmlFile jf) throws IOException {
		s.writeByte(getNodeType());
		vars.save(config, s, jf);
		body.save(config, s, jf);
	}

	public void garbageIdent() {
		vars.garbageIdent();
		body.garbageIdent();
	}

	public void getFields(Set fields) {
		body.getFields(fields);
	}

	static final long serialVersionUID = 5392132877428547506L;

	public BasicType getBasicType() {
		return BasicType.PropType;
	}

}