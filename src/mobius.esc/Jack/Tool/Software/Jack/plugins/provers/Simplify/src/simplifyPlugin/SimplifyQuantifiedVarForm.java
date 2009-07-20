//******************************************************************************
/* Copyright (c) 2003 INRIA. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: 
/*
/*******************************************************************************
/* Warnings/Remarks:
/******************************************************************************/

package simplifyPlugin;

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
public class SimplifyQuantifiedVarForm
	extends QuantifiedVarForm
	implements ITranslatable {

	SimplifyQuantifiedVarForm(QuantifiedVarForm qvf) {
		//		var = new SimplifyTerminalForm(qvf.getVar());
		//		type = Languages.getClass("B").formulaFactory(qvf.getType());
		//		if (qvf.getNext() != null)
		//			next = new SimplifyQuantifiedVarForm(qvf.getNext());
		super(qvf);
	}

	public ITranslationResult toLang(int indent) throws LanguageException {
		SimplifyTranslationResult str = appendVarsSimplify(indent);
		return new SimplifyTranslationResult(str, str.toUniqString());
	}

	/**
	 * append the list of variables to the buffer in a format suitable for using
	 * as a variable declaration for a quantified formula in the Simplify prover.
	 */
	//	public SimplifyTranslationResult appendSimplify(int indent)
	//		throws LanguageException {
	//		SimplifyTranslationResult str = appendVarsSimplify(indent);
	//		return new SimplifyTranslationResult(
	//			str,
	//			"(" + str.toUniqString() + ")");
	//	}

	/**
	 * Print the list of variables separated by spaces to buf.
	 */
	SimplifyTranslationResult appendVarsSimplify(int indent)
		throws LanguageException {
		SimplifyTranslationResult str =
			(SimplifyTranslationResult) var.toLang("Simplify", indent);
		if (next != null) {
			SimplifyTranslationResult str1 =
				(SimplifyTranslationResult) next.toLang("Simplify", indent);
			str =
				new SimplifyTranslationResult(
					str,
					str1,
					str.toUniqString() + " " + str1.toUniqString());
		}
		return str;
	}

}
