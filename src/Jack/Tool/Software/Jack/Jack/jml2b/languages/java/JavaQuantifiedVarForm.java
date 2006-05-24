//******************************************************************************
/* Copyright (c) 2003, 2004 INRIA. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: 
/*
/*******************************************************************************
/* Warnings/Remarks:
/******************************************************************************/

package jml2b.languages.java;

import jml2b.exceptions.LanguageException;
import jml2b.formula.QuantifiedVarForm;
import jml2b.languages.ITranslatable;
import jml2b.languages.ITranslationResult;

/**
 * @author L. Burdy
 */
public class JavaQuantifiedVarForm
	extends QuantifiedVarForm
	implements ITranslatable {

	JavaQuantifiedVarForm(QuantifiedVarForm qvf) {
		super(qvf);
	}

	/**
	 * Converts the quantified formulas to a string suitable for output into
	 * the Java view.
	 * @param indent The current indentation
	 * @return the list of variable with their type
	 **/
	public ITranslationResult toLang(int indent) throws LanguageException {
		String res = var.toLangDefault(indent + 3);
		if (next != null)
			res += ", " + next.toLang("Java", indent + 3).toUniqString();
		return new JavaTranslationResult(res, 0);

	}

}
