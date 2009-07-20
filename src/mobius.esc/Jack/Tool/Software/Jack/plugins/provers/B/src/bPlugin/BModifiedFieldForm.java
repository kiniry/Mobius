//******************************************************************************
/* Copyright (c) 2003, 2004 INRIA. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: 
/*
/*******************************************************************************
/* Warnings/Remarks:
/******************************************************************************/

package bPlugin;

import jml2b.exceptions.LanguageException;
import jml2b.formula.ModifiedFieldForm;
import jml2b.languages.ITranslatable;
import jml2b.languages.ITranslationResult;

/**
 * @author L. Burdy
 **/
public class BModifiedFieldForm extends ModifiedFieldForm implements ITranslatable {

	static final long serialVersionUID = -4459684249262184283L;

	BModifiedFieldForm(ModifiedFieldForm f) {
		super(f);
	}

	public ITranslationResult toLang(int indent) throws LanguageException {
		return new BTranslationResult(getNodeText());
	}
}
