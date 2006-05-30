//******************************************************************************
/* Copyright (c) 2003, 2004 INRIA. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: 
/*
/*******************************************************************************
/* Warnings/Remarks:
/******************************************************************************/

package pvsPlugin;

import jml2b.exceptions.LanguageException;
import jml2b.formula.QuantifiedVarForm;
import jml2b.languages.ITranslatable;
import jml2b.languages.ITranslationResult;

/**
 * @author lburdy
 *
 * To change the template for this generated type comment go to
 * Window&gt;Preferences&gt;Java&gt;Code Generation&gt;Code and Comments
 */
public class PvsQuantifiedVarForm
	extends QuantifiedVarForm
	implements ITranslatable {

	/**
	 * @param qvf
	 */
	public PvsQuantifiedVarForm(QuantifiedVarForm qvf) {
		super(qvf);
	}

	public ITranslationResult toLang(int indent) throws LanguageException {
		return null;
	}
}
