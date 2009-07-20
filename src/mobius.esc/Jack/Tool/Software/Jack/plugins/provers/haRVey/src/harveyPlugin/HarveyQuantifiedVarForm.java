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
import jml2b.formula.QuantifiedVarForm;
import jml2b.languages.ITranslatable;
import jml2b.languages.ITranslationResult;

/**
 * @author lburdy
 *
 * To change the template for this generated type comment go to
 * Window&gt;Preferences&gt;Java&gt;Code Generation&gt;Code and Comments
 */
public class HarveyQuantifiedVarForm
	extends QuantifiedVarForm
	implements ITranslatable {

	HarveyQuantifiedVarForm(QuantifiedVarForm qvf) {
		super(qvf);
	}

	public ITranslationResult toLang(int indent) throws LanguageException {
		HarveyTranslationResult str = appendVarsSimplify(indent);
		return new HarveyTranslationResult(
			str,
			str.toUniqString());
	}

	/**
	 * Print the list of variables separated by spaces to buf.
	 */
	HarveyTranslationResult appendVarsSimplify(int indent)
		throws LanguageException {
		HarveyTranslationResult str =
			(HarveyTranslationResult) var.toLang("Harvey", indent);
		if (next != null) {
			HarveyTranslationResult str1 =
				(HarveyTranslationResult) next.toLang("Harvey", indent);
			str =
				new HarveyTranslationResult(
					str,
					str1,
					str.toUniqString() + " " + str1.toUniqString());
		}
		return str;
	}

}
