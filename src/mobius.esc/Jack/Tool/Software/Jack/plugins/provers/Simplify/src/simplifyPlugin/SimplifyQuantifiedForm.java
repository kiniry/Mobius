//******************************************************************************
/* Copyright (c) 2003 INRIA. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: 
/*
/*******************************************************************************
/* Warnings/Remarks:
/******************************************************************************/

package simplifyPlugin;

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
public class SimplifyQuantifiedForm extends QuantifiedForm implements ITranslatable {

	/**
	 * 
	 */
	private static final long serialVersionUID = 1L;

	SimplifyQuantifiedForm(QuantifiedForm f) {
		super(f);
	}

	public ITranslationResult toLang(int indent) throws LanguageException {
		String res = "";
		switch (getNodeType()) {
			case Jm_FORALL :
				res += "(FORALL (";
				break;
			case Jm_EXISTS :
				res += "(EXISTS (";
				break;
			default :
				throw new InternalError(
					"QuantifiedForm.appendSimplify: unhandled case: "
						+ toString[getNodeType()]);
		}
		SimplifyTranslationResult str =
			(SimplifyTranslationResult) vars.toLang("Simplify", indent);

		res += str.toUniqString() + ") ";

		SimplifyTranslationResult str1 =
			(SimplifyTranslationResult) body.toLang("Simplify", indent);

//		String[] st = str1.toStrings();
//		for (int i = 0; i < st.length; i++)
//			res += "(IMPLIES " + st[i] + " ";
//		res += str1.toUniqString();
//		for (int i = 0; i < st.length; i++)
//			res += ")";
		res += str1.toUniqString();
		res += ")\n";
		return new SimplifyTranslationResult(str, str1, res);
	}

}
