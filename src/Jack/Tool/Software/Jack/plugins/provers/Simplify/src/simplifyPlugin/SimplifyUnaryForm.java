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
import jml2b.formula.UnaryForm;
import jml2b.languages.ITranslatable;
import jml2b.languages.ITranslationResult;

/**
 * @author lburdy
 *
 * To change the template for this generated type comment go to
 * Window&gt;Preferences&gt;Java&gt;Code Generation&gt;Code and Comments
 */
public class SimplifyUnaryForm
	extends UnaryForm
	implements ITranslatable {

	/**
	 * 
	 */
	private static final long serialVersionUID = 1L;

	SimplifyUnaryForm(UnaryForm f) {
		super(f);
	}

	public ITranslationResult toLang(int indent) throws LanguageException {
		SimplifyTranslationResult str =
			(SimplifyTranslationResult) exp.toLang("Simplify", indent);
		switch (getNodeType()) {
			case Jm_T_OLD :
				return str;
			case Ja_LNOT :
				return new SimplifyTranslationResult(
					str,
					"(NOT " + str.toUniqString() + ")");
			case Ja_UNARY_NUMERIC_OP :
				return new SimplifyTranslationResult(
					str,
					"(* -1 " + str.toUniqString() + ")");
			case B_BOOL :
				{
					String name = SimplifyLanguage.newName();
					return new SimplifyTranslationResult(
						str,
						"(IFF "
							+ str.toUniqString()
							+ " (EQ "
							+ name
							+ " |@true|))",
						"(IFF (NOT "
							+ str.toUniqString()
							+ ") (EQ "
							+ name
							+ " |@false|))",
						name);
				}
			case B_ACCOLADE :
				{
					String name = SimplifyLanguage.newName();
					String x = SimplifyLanguage.newName();
					SimplifyTranslationResult str1 =
						SimplifyBinaryForm.in(
							new SimplifyTranslationResult(x),
							new SimplifyTranslationResult(name));
					return new SimplifyTranslationResult(
						str,
						"(FORALL ("
							+ x
							+ ") (IFF "
							+ str1.toUniqString()
							+ "(EQ "
							+ x
							+ " "
							+ str.toUniqString()
							+ ")))",
						name);
				}
			case B_DOM :
				// x : dom(f) is considered to be always true.
				String name = SimplifyLanguage.newName();
				String x = SimplifyLanguage.newName();
				SimplifyTranslationResult str1 =
					SimplifyBinaryForm.in(
						new SimplifyTranslationResult(x),
						new SimplifyTranslationResult(name));
				return new SimplifyTranslationResult(
					str,
					"(FORALL (" + x + ") " + str1.toUniqString() + ")",
					name);
			default :
				throw new InternalError(
					"SimplifyUnaryForm.toLang: "
						+ "default case should not be reached "
						+ getNodeType());
		}

	}

}
