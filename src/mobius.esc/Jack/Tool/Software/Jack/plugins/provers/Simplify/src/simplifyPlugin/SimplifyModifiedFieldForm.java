//******************************************************************************
/* Copyright (c) 2003 INRIA. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: 
/*
/*******************************************************************************
/* Warnings/Remarks:
/******************************************************************************/

package simplifyPlugin;

import jml2b.exceptions.LanguageException;
import jml2b.formula.ModifiedFieldForm;
import jml2b.languages.ITranslatable;
import jml2b.languages.ITranslationResult;

/**
 * @author L. Burdy
 **/
public class SimplifyModifiedFieldForm extends ModifiedFieldForm implements ITranslatable {

	/**
	 * 
	 */
	private static final long serialVersionUID = 3642026392187991364L;

	SimplifyModifiedFieldForm(ModifiedFieldForm f) {
		super(f);
	}

	public ITranslationResult toLang(int indent) throws LanguageException {
		return new SimplifyTranslationResult("|" + getNodeText() + "|");
	}
}
