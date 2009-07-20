//******************************************************************************
/* Copyright (c) 2003, 2004 INRIA. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: 
/*
/*******************************************************************************
/* Warnings/Remarks:
/******************************************************************************/

package jml2b.formula;

import jml2b.structure.AField;
import jml2b.structure.java.Identifier;

/**
 * @author L. Burdy
 **/
public class ModifiedFieldForm extends TerminalForm {

	/**
	 * 
	 */
	private static final long serialVersionUID = 1L;
	protected final IModifiesField m;

	public ModifiedFieldForm(ModifiedFieldForm f) {
		super(IFormToken.MODIFIED_FIELD);
		nodeText = f.getNodeText();
		ident = f.ident;
		this.m = f.m;
	}

	public ModifiedFieldForm(AField f, IModifiesField m) {
		super(IFormToken.MODIFIED_FIELD);
		nodeText = f.newName();
		ident = new Identifier(f);
		this.m = m;
	}

}
