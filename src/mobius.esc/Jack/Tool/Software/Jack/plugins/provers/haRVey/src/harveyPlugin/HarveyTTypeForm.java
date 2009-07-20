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
import jml2b.formula.TTypeForm;
import jml2b.languages.ITranslatable;
import jml2b.languages.ITranslationResult;

/**
 * @author lburdy
 *
 * To change the template for this generated type comment go to
 * Window&gt;Preferences&gt;Java&gt;Code Generation&gt;Code and Comments
 */
public class HarveyTTypeForm extends TTypeForm implements ITranslatable {

	/**
	 * 
	 */
	private static final long serialVersionUID = 1L;

	HarveyTTypeForm(TTypeForm f) {
		super(f);
	}

	public ITranslationResult toLang(int indent) throws LanguageException {
		if (type == null)
			return new HarveyTranslationResult(nodeText);
		else
			return type.toLang("Harvey");
	}

}
