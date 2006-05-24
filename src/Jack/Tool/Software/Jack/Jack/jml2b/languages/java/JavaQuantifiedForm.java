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
import jml2b.formula.QuantifiedForm;
import jml2b.languages.ITranslatable;
import jml2b.languages.ITranslationResult;

/**
 * @author L. Burdy
 */
public class JavaQuantifiedForm extends QuantifiedForm implements ITranslatable {

	/**
	 * 
	 */
	private static final long serialVersionUID = 1L;

	JavaQuantifiedForm(QuantifiedForm f) {
		super(f);
	//	vars = new JavaQuantifiedVarForm(vars);
	}

	/**
	 * The formula is displayed <code>\forall vars; body</code> or 
	 * <code>\exists vars; body</code>
	 **/
	public ITranslationResult toLang(int indent) throws LanguageException {
		String res = null;
		switch (getNodeType()) {
			case Jm_FORALL :
				res = "\\forall ";
				break;
			case Jm_EXISTS :
				res = "\\exists ";
				break;
		}
		res += vars.getType().toLangDefault(indent);
		res += " " + vars.toLang("Java", indent).toUniqString() + " ; ";
		res += body.toLangDefault(indent + 3);
		return new JavaTranslationResult(res,
		JavaLanguage.priority[getNodeType()]);
	}
}
