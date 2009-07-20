//******************************************************************************
/* Copyright (c) 2004 INRIA. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: 
/*
/*******************************************************************************
/* Warnings/Remarks:
/******************************************************************************/

package jml2b.languages;

import jml2b.exceptions.LanguageException;

/**
 * This interface defines a translatable object: a formula or a type.
 * 
 * @author L. Burdy
 **/
public interface ITranslatable {

	/**
	 * Translate a formula, a type or quantified variables.
	 * @param indent
	 * @return the result of the translation.
	 * @throws LanguageException
	 */
	public ITranslationResult toLang(int indent) throws LanguageException;

}
