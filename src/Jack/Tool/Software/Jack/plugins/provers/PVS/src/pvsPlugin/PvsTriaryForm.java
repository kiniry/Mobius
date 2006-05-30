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
import jml2b.formula.TriaryForm;
import jml2b.languages.ITranslatable;
import jml2b.languages.ITranslationResult;

/**
 * @author lburdy
 *
 * To change the template for this generated type comment go to
 * Window&gt;Preferences&gt;Java&gt;Code Generation&gt;Code and Comments
 */
public class PvsTriaryForm extends TriaryForm implements ITranslatable {

	/**
	 * 
	 */
	private static final long serialVersionUID = 1L;

	/**
	 * @param form
	 */
	public PvsTriaryForm(TriaryForm form) {
		super(form);
	}

	public ITranslationResult toLang(int indent) throws LanguageException {
		switch (getNodeType()) {
			case B_ARRAY_EQUALS :
				{
					String x = PvsLanguage.newName();
					PvsTranslationResult str1 =
						(PvsTranslationResult) f1.toLang("PVS", indent);
					PvsTranslationResult str2 =
						(PvsTranslationResult) left.toLang("PVS", indent);
					PvsTranslationResult str3 =
						(PvsTranslationResult) right.toLang("PVS", indent);
					return new PvsTranslationResult(
						"FORALL ("
							+ x
							+ ":posnat): (0 <= "
							+ x
							+ " AND "
							+ x
							+ "< arraylength("
							+ str1.toUniqString()
							+ ")) => "
							+ str2.toUniqString()
							+ "("
							+ str1.toUniqString()
							+ ")("
							+ x
							+ ") = "
							+ str3.toUniqString()
							+ "("
							+ str1.toUniqString()
							+ ")("
							+ x
							+ ")");
				}
			case NEW_OBJECT :
				{
					String x = PvsLanguage.newName();
					PvsTranslationResult str1 =
						(PvsTranslationResult) f1.toLang("PVS", indent);
					PvsTranslationResult str2 =
						(PvsTranslationResult) left.toLang("PVS", indent);
					PvsTranslationResult str3 =
						(PvsTranslationResult) right.toLang("PVS", indent);
					return new PvsTranslationResult(
						"FORALL ("
							+ x
							+ ":REFERENCES): "
							+ x
							+ " /= "
							+ str1.toUniqString()
							+ " => "
							+ str2.toUniqString()
							+ "("
							+ x
							+ ") = "
							+ str3.toUniqString()
							+ "("
							+ x
							+ ")");
				}
			case Ja_QUESTION :
				return new PvsTranslationResult(
					"IF "
						+ f1.toLang("PVS", indent).toUniqString()
						+ " THEN "
						+ left.toLang("PVS", indent).toUniqString()
						+ " ELSE "
						+ right.toLang("PVS", indent).toUniqString()
						+ " ENDIF");
			case ARRAY_RANGE :
				{
					String x = PvsLanguage.newName();
					String y = PvsLanguage.newName();
					String z = PvsLanguage.newName();
					PvsTranslationResult str1 =
						(PvsTranslationResult) f1.toLang("PVS", indent);
					PvsTranslationResult str2 =
						(PvsTranslationResult) left.toLang("PVS", indent);
					PvsTranslationResult str3 =
						(PvsTranslationResult) right.toLang("PVS", indent);
					return new PvsTranslationResult(
						str1,
						str2,
						str3,
						"(LAMBA ("
							+ x
							+ ":"
							+ PvsLanguage.basicType(
								f1.getBasicType().getRtype().getRtype())
							+ "): (EXISTS ("
							+ y
							+ ":"
							+ PvsLanguage.basicType(right.getBasicType())
							+ "): "
							+ str3.toUniqString()
							+ "("
							+ y
							+ ") AND (EXISTS ("
							+ z
							+ ": "
							+ PvsLanguage.basicType(left.getBasicType())
							+ "): "
							+ str1.toUniqString()
							+ "("
							+ z
							+ ") AND "
							+ str2.toUniqString()
							+ "("
							+ z
							+ ")("
							+ y
							+ ") = "
							+ x
							+ ")))");
				}
			default :
				throw new InternalError(
					"PvsTriaryForm.toLang: case not implemented: "
						+ toString[getNodeType()]);

		}

	}

	PvsTranslationResult equalsSubsDomToPvs(String x, int indent)
		throws LanguageException {
		switch (getNodeType()) {
			case B_ARRAY_EQUALS :
				{
					PvsTranslationResult ctr1 =
						(PvsTranslationResult) getF1().toLang("PVS", indent);
					PvsTranslationResult ctr2 =
						(PvsTranslationResult) getLeft().toLang("PVS", indent);
					PvsTranslationResult ctr3 =
						(PvsTranslationResult) getRight().toLang("PVS", indent);
					return new PvsTranslationResult(
						ctr1,
						ctr2,
						ctr3,
						"(0 <= "
							+ x
							+ " AND "
							+ x
							+ "< arraylength("
							+ ctr1.toUniqString()
							+ ")) =>"
							+ ctr2.toUniqString()
							+ "("
							+ ctr1.toUniqString()
							+ ")("
							+ x
							+ ") = "
							+ ctr3.toUniqString()
							+ "("
							+ ctr1.toUniqString()
							+ ")("
							+ x
							+ ")");
				}
			default :
				throw new InternalError(
					"PvsTriaryForm.equalsSubsDomToPvs(String) bad node type: "
						+ right.getNodeType());
		}
	}

}
