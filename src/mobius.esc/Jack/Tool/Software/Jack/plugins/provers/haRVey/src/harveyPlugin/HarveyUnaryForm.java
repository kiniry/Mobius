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
import jml2b.exceptions.TranslationException;
import jml2b.formula.UnaryForm;
import jml2b.languages.ITranslatable;
import jml2b.languages.ITranslationResult;

/**
 * @author lburdy
 *
 * To change the template for this generated type comment go to
 * Window&gt;Preferences&gt;Java&gt;Code Generation&gt;Code and Comments
 */
public class HarveyUnaryForm
	extends UnaryForm
	implements ITranslatable {

	/**
	 * 
	 */
	private static final long serialVersionUID = 1L;

	HarveyUnaryForm(UnaryForm f) {
		super(f);
	}

	public ITranslationResult toLang(int indent) throws LanguageException {
		HarveyTranslationResult str =
			(HarveyTranslationResult) exp.toLang("Harvey", indent);
		switch (getNodeType()) {
			case Jm_T_OLD :
				return str;
			case Ja_LNOT :
				return new HarveyTranslationResult(
					str,
					"(not " + str.toUniqString() + ")");
			case Ja_UNARY_NUMERIC_OP :
//				return new HarveyTranslationResult(
//					str,
//					"(* -1 " + str.toUniqString() + ")");
			throw new TranslationException(
				"Harvey translator does not handle " + getNodeType());

			case B_BOOL :
				{
					String name = HarveyLanguage.newName();
					return new HarveyTranslationResult(
						str,
						"(<-> "
							+ str.toUniqString()
							+ " (= "
							+ name
							+ " tt))",
						"(<-> (not "
							+ str.toUniqString()
							+ ") (= "
							+ name
							+ " ff))",
						name);
				}
			case B_ACCOLADE :
				{
					String name = HarveyLanguage.newName();
					String x = HarveyLanguage.newName();
					HarveyTranslationResult str1 =
						HarveyBinaryForm.in(
							new HarveyTranslationResult(x),
							new HarveyTranslationResult(name));
					return new HarveyTranslationResult(
						str,
						"(forall "
							+ x
							+ " (<-> "
							+ str1.toUniqString()
							+ "(= "
							+ x
							+ " "
							+ str.toUniqString()
							+ ")))",
						name);
				}
			case B_DOM :
				// x : dom(f) is considered to be always true.
				String name = HarveyLanguage.newName();
				String x = HarveyLanguage.newName();
				HarveyTranslationResult str1 =
					HarveyBinaryForm.in(
						new HarveyTranslationResult(x),
						new HarveyTranslationResult(name));
				return new HarveyTranslationResult(
					str,
					"(forall " + x + " " + str1.toUniqString() + ")",
					name);
			default :
				throw new InternalError(
					"HarveyUnaryForm.toLang: "
						+ "default case should not be reached "
						+ getNodeType());
		}

	}


}
