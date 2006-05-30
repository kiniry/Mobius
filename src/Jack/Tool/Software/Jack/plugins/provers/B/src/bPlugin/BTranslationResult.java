//******************************************************************************
/* Copyright (c) 2003, 2004 INRIA. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: 
/*
/*******************************************************************************
/* Warnings/Remarks:
/******************************************************************************/

package bPlugin;

import jml2b.languages.ITranslationResult;

/**
 * @author lburdy
 *
 * To change the template for this generated type comment go to
 * Window&gt;Preferences&gt;Java&gt;Code Generation&gt;Code and Comments
 */
public class BTranslationResult implements ITranslationResult {

	String s;

	public BTranslationResult() {
	}

	BTranslationResult(String s) {
		this.s = s;
	}

	public ITranslationResult Factory(String s) {
		return new BTranslationResult(s);
	}

	public String toUniqString() {
		return s;
	}

}
