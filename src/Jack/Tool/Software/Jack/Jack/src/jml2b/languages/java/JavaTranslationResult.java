//******************************************************************************
/* Copyright (c) 2003, 2004 INRIA. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: 
/*
/*******************************************************************************
/* Warnings/Remarks:
/******************************************************************************/

package jml2b.languages.java;

import jml2b.formula.IFormToken;
import jml2b.languages.ITranslationResult;

/**
 * @author L. Burdy
 */
public class JavaTranslationResult implements ITranslationResult {

	private String s;

	private int priority;

	JavaTranslationResult() {
	}

	JavaTranslationResult(String s, int p) {
		this.s = s;
		priority = p;
	}

	public ITranslationResult Factory(String s) {
		return new JavaTranslationResult(
			s,
			JavaLanguage.priority[IFormToken.Ja_IDENT]);
	}

	public String toUniqString() {
		return s;
	}

	public String[] toStrings() {
		String[] st = { s };
		return st;
	}

	public int getPriority() {
		return priority;
	}

	public String toString() {
		return s;
	}

}
