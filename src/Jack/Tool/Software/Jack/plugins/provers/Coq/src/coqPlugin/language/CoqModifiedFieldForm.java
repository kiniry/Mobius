//******************************************************************************
/* Copyright (c) 2003, 2004 INRIA. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: 
/*
/*******************************************************************************
/* Warnings/Remarks:
/******************************************************************************/

package coqPlugin.language;

import coqPlugin.CoqTranslationResult;
import jml2b.exceptions.LanguageException;
import jml2b.formula.ModifiedFieldForm;
import jml2b.languages.ITranslatable;
import jml2b.languages.ITranslationResult;

/**
 * @author lburdy
 *
 * To change the template for this generated type comment go to
 * Window&gt;Preferences&gt;Java&gt;Code Generation&gt;Code and Comments
 */
public class CoqModifiedFieldForm
	extends ModifiedFieldForm
	implements ITranslatable {

	/**
	 * 
	 */
	private static final long serialVersionUID = 4960961226953618633L;

	/**
	 * @param form
	 */
	public CoqModifiedFieldForm(ModifiedFieldForm form) {
		super(form);
	}

	public ITranslationResult toLang(int indent) throws LanguageException {
		String name =getNodeText();
		CoqVar.putStupidName(name);
		name = CoqVar.getCoqName(name);
		return new CoqTranslationResult(name);
	}
}
