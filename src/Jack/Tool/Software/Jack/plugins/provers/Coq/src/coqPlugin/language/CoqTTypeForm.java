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
import jml2b.formula.TTypeForm;
import jml2b.languages.ITranslatable;
import jml2b.languages.ITranslationResult;

/**
 * @author lburdy
 *
 * To change the template for this generated type comment go to
 * Window&gt;Preferences&gt;Java&gt;Code Generation&gt;Code and Comments
 */
public class CoqTTypeForm extends TTypeForm implements ITranslatable {

	/**
	 * 
	 */
	private static final long serialVersionUID = 1L;

	/**
	 * @param form
	 */
	public CoqTTypeForm(TTypeForm form) {
		super(form);
	}

	public ITranslationResult toLang(int indent) throws LanguageException {
		if (type == null)
			return new CoqTranslationResult(nodeText);
		else {
			if(isNative()) {
				return new CoqTranslationResult(getRefType().getBName());
			}
			else {
				return type.toLang("Coq");
			}
		}
	}
}
