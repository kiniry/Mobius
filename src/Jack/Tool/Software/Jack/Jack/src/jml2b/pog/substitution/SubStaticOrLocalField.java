//******************************************************************************
/* Copyright (c) 2004 INRIA. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: 
/*
/*******************************************************************************
/* Warnings/Remarks:
/******************************************************************************/
package jml2b.pog.substitution;

import jml2b.formula.Formula;

/**
 * @author lburdy
 *
 * To change the template for this generated type comment go to
 * Window&gt;Preferences&gt;Java&gt;Code Generation&gt;Code and Comments
 */
public class SubStaticOrLocalField extends SubForm {

	public SubStaticOrLocalField(Formula a, Formula b) {
		super(a, b);
	}

	public Object clone() {
		return new SubStaticOrLocalField(old, (Formula) newF.clone());
	}

	public Formula getField() {
		return old;
	}

}
