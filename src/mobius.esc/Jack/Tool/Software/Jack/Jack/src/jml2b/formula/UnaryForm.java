//******************************************************************************
/* Copyright (c) 2002, 2003 GEMPLUS Software Research Labs. All Rights Reserved.
/* Copyright (c) 2003, 2004 INRIA. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: UnaryForm.java
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
import jml2b.exceptions.InternalError;
import jml2b.exceptions.LoadException;
import jml2b.structure.java.IJmlFile;
import jml2b.util.IOutputStream;
import jml2b.util.JpoInputStream;

/**
 * This class implements unary Formula.
 * The node type can be :
 * <UL>
 * <li> B_ACCOLADE
 * <li> B_BOOL
 * <li> B_DOM
 * <li> Ja_UNARY_NUMERIC_OP
 * <li> Ja_LNOT
 * <li> Jm_T_OLD
 * </UL>
 * @author L. Burdy
 **/
public class UnaryForm extends Formula {

	/**
	 * The leaf formula.
	 **/
	protected Formula exp;

	/*@
	  @ private invariant exp != null;
	  @*/

	public UnaryForm(UnaryForm f) {
		super(f.getNodeType());
		exp = f.exp;
	}

	/**
	 * Constructs a unary formula from a loaded jpo file.
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
	UnaryForm(
		IJml2bConfiguration config,
		IJmlFile fi,
		byte nodeType,
		JpoInputStream s)
		throws IOException, LoadException {
		super(nodeType);
		exp = Formula.create(config, s, fi);
	}

	/**
	 * Constructs a unary formula from a formula and a token.
	 * @param nodeType token of the new formula
	 * @param exp part of the new formula
	 **/
	/*@
	  @ requires exp != null;
	  @*/
	public UnaryForm(byte nodeType, Formula exp) {
		super(nodeType);
		this.exp = exp;
	}

	public Object clone() {
		UnaryForm res = new UnaryForm(getNodeType(), (Formula) exp.clone());
		return res;
	}

	public Formula sub(Formula a, Formula b, boolean subInCalledOld) {
		switch (getNodeType()) {
			case IFormToken.Jm_T_OLD :
			case IFormToken.T_VARIANT_OLD :
				return this;
			case IFormToken.T_CALLED_OLD :
				if (!subInCalledOld) {
					return this;
				}
			default :
				Formula tmpexp = exp.sub(a, b, subInCalledOld);
				if (tmpexp == exp)
					return this;
				else
					return new UnaryForm(getNodeType(), tmpexp);
		}
	}

	public Formula suppressSpecialOld(int token) {
		if (getNodeType() == token)
			return exp.suppressSpecialOld(token);
		else {
			Formula tmpexp = exp.suppressSpecialOld(token);
			if (tmpexp == exp)
				return this;
			else
				return new UnaryForm(getNodeType(), tmpexp);
		}
	}

	public void processIdent() {
		exp.processIdent();
	}

	public Formula instancie(Formula b) {
		exp = exp.instancie(b);
		return this;
	}

	public void garbageIdent() {
		exp.garbageIdent();
	}

	public void getFields(Set fields) {
		exp.getFields(fields);
	}

	public Formula subIdent(String a, Formula b) {
		switch (getNodeType()) {
			case IFormToken.Jm_T_OLD :
				return this;
			default :
				Formula tmpexp = exp.subIdent(a, b);
				if (tmpexp == exp)
					return this;
				else
					return new UnaryForm(getNodeType(), tmpexp);
		}
	}

	/*@
	  @ requires f != null;
	  @*/
	public boolean equals(Object f) {
		return getNodeType() == ((Formula) f).getNodeType()
			&& exp.equals(((UnaryForm) f).exp);
	}

	/*@
	  @ requires f != null;
	  @*/
	public boolean is(Formula f) {
		return getNodeType() == f.getNodeType() && exp.is(((UnaryForm) f).exp);
	}

	public int contains(Vector selectedFields) {
		return exp.contains(selectedFields);
	}

	public boolean isObvious(boolean atTheEnd) {
		if (getNodeType() == Ja_LNOT)
			return !exp.isObvious(atTheEnd);
		else
			return false;
	}

	/*@
	  @ requires s != null;
	  @*/
	public void save(IJml2bConfiguration config, IOutputStream s, IJmlFile jf) throws IOException {
		s.writeByte(getNodeType());
		exp.save(config, s, jf);
	}

	/**
	 * Returns the leaf formula.
	 * @return <code>exp</code>
	 */
	public Formula getExp() {
		return exp;
	}

	static final long serialVersionUID = -5114454662274275537L;

	public BasicType getBasicType() {
		switch (getNodeType()) {
			case Jm_T_OLD :
				return exp.getBasicType();
			case Ja_LNOT :
				return BasicType.PropType;
			case Ja_UNARY_NUMERIC_OP :
				return BasicType.ZType;
			case B_ACCOLADE :
				return new BasicType(exp.getBasicType(), BasicType.PropType);
			case B_DOM :
				return new BasicType(exp.getBasicType().getLtype(), BasicType.PropType);
			case B_BOOL :
				return  BasicType.BoolType;
			default :
				throw new InternalError(
					"UnaryForm.getBasicType(): "
						+ "default case should not be reached "
						+ getNodeType());
		}
	}

}