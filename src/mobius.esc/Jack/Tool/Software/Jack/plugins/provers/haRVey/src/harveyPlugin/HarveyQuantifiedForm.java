//******************************************************************************
/* Copyright (c) 2003, 2004 INRIA. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: 
/*
/*******************************************************************************
/* Warnings/Remarks:
/******************************************************************************/

package harveyPlugin;

import jml2b.exceptions.InternalError;
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
public class HarveyQuantifiedForm extends QuantifiedForm implements ITranslatable {

	/**
	 * 
	 */
	private static final long serialVersionUID = 1L;

	HarveyQuantifiedForm(QuantifiedForm f) {
		super(f);
	}

	public ITranslationResult toLang(int indent) throws LanguageException {
		String res = "";
		switch (getNodeType()) {
			case Jm_FORALL :
				res += "(forall ";
				break;
			case Jm_EXISTS :
				res += "(exists ";
				break;
			default :
				throw new InternalError(
					"HarveyQuantifiedForm.toLang: unhandled case: "
						+ toString[getNodeType()]);
		}
		HarveyTranslationResult str =
			(HarveyTranslationResult) vars.toLang("Harvey", indent);

		res += str.toUniqString() + " ";

		HarveyTranslationResult str1 =
			(HarveyTranslationResult) body.toLang("Harvey", indent);

		String[] st = str1.toStrings();
		for (int i = 0; i < st.length; i++)
			res += "(-> " + st[i] + " ";
		res += str1.toUniqString();
		for (int i = 0; i < st.length; i++)
			res += ")";
		res += ")\n";
		return new HarveyTranslationResult(str, res);
	}

}
