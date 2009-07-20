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
import jml2b.formula.TTypeForm;
import jml2b.languages.ITranslatable;
import jml2b.languages.ITranslationResult;

/**
 * @author L. Burdy
 */
public class JavaTTypeForm extends TTypeForm implements ITranslatable {

	/**
	 * 
	 */
	private static final long serialVersionUID = 1L;

	JavaTTypeForm(TTypeForm f) {
		super(f);
	}

	public ITranslationResult toLang(int indent) throws LanguageException {
		return new JavaType(type).toLang(indent);
	}
}
