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

import java.util.Set;
import java.util.Vector;

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


	public int contains(Vector selectedFields) {
		return body.contains(selectedFields);
	}
	
	public boolean isObvious(boolean atTheEnd) {
		return false;
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