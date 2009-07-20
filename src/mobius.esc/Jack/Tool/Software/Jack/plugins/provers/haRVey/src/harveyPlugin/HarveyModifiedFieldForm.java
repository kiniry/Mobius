//******************************************************************************
/* Copyright (c) 2003, 2004 INRIA. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: 
/*
/*******************************************************************************
/* Warnings/Remarks:
/******************************************************************************/

package harveyPlugin;

import jml2b.exceptions.LanguageException;
import jml2b.formula.ModifiedFieldForm;
import jml2b.languages.ITranslatable;
import jml2b.languages.ITranslationResult;

/**
 * @author L. Burdy
 **/
public class HarveyModifiedFieldForm extends ModifiedFieldForm implements ITranslatable {

	/**
	 * 
	 */
	private static final long serialVersionUID = 1L;

	HarveyModifiedFieldForm(ModifiedFieldForm f) {
		super(f);
	}

	public ITranslationResult toLang(int indent) throws LanguageException {
		return new HarveyTranslationResult(getNodeText());
	}
}
