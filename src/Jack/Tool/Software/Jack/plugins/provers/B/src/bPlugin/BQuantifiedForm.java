//******************************************************************************
/* Copyright (c) 2002, 2003 GEMPLUS Software Research Labs. All Rights Reserved.
/* Copyright (c) 2003, 2004 INRIA. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: 
/*
/*******************************************************************************
/* Warnings/Remarks:
/******************************************************************************/

package bPlugin;

import jml2b.exceptions.LanguageException;
import jml2b.formula.QuantifiedForm;
import jml2b.languages.ITranslatable;
import jml2b.languages.ITranslationResult;

/**
 * @author lburdy
 *
 * To change the template for this generated type comment go to
 * Window&gt;Preferences&gt;Java&gt;Code Generation&gt;Code and Comments
 */
public class BQuantifiedForm
	extends QuantifiedForm
	implements ITranslatable {

	static final long serialVersionUID = -8752912059420086488L;
	String lang;

	BQuantifiedForm(String lang, QuantifiedForm f) {
		super(f);
		this.lang = lang;
	}

	public ITranslationResult toLang(int indent) throws LanguageException {
		String res = null;
		switch (getNodeType()) {
			case Jm_FORALL :
				res = "!(" + vars.toLang(lang, indent).toUniqString() + " => ";
				break;
			case Jm_EXISTS :
				res = "#(" + vars.toLang(lang, indent).toUniqString() + " & ";
				break;
		}
		if (BLanguage.priority[body.getNodeType()]
			<= BLanguage.priority[Jm_IMPLICATION_OP]) {
			res += "(" + body.toLang(lang, indent).toUniqString() + ")";
		} else
			res += body.toLang(lang, indent).toUniqString();
		res += ")";
		return new BTranslationResult(res);
	}

}
