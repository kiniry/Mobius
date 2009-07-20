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
import jml2b.formula.TriaryForm;
import jml2b.languages.ITranslatable;
import jml2b.languages.ITranslationResult;

/**
 * @author lburdy
 *
 * To change the template for this generated type comment go to
 * Window&gt;Preferences&gt;Java&gt;Code Generation&gt;Code and Comments
 */
public class HarveyTriaryForm extends TriaryForm implements ITranslatable {

	/**
	 * 
	 */
	private static final long serialVersionUID = 1L;

	HarveyTriaryForm(TriaryForm f) {
		super(f);
	}

	/**
	 * Converts for ouput suitable for simplify.
	 * <code> cond ? a : b</code> is converted to
	 * <code> (AND (IMPLIES cond a) (IMPLIES (NOT cond) b))</code>
	 */
	public ITranslationResult toLang(int indent) throws LanguageException {
		switch (getNodeType()) {
			case B_ARRAY_EQUALS :
				{
					String x = HarveyLanguage.newName();
					
					HarveyTranslationResult str1 =
						equalsSubsDomToSimmplify(x, indent);
					return new HarveyTranslationResult(
						str1,
						"(forall "
							+ x
							+ " "
							+ str1.toUniqString()
							+ ")");
				}
			case NEW_OBJECT :
				{
					String x = HarveyLanguage.newName();
					HarveyTranslationResult str1 =
						(HarveyTranslationResult) f1.toLang("Harvey", indent);
					HarveyTranslationResult str2 =
						(HarveyTranslationResult) left.toLang("Harvey", indent);
					HarveyTranslationResult str3 =
						(HarveyTranslationResult) right.toLang(
							"Harvey",
							indent);
					return new HarveyTranslationResult(
						str1,
						str2,
						str3,
						"(forall "
							+ x
							+ " (-> (not (="
							+ x
							+ " "
							+ str1.toUniqString()
							+ "))"
							+ "(= (select "
							+ str2.toUniqString()
							+ " "
							+ x
							+ ") (select "
							+ str3.toUniqString()
							+ " "
							+ x
							+ "))))");
				}
			case ARRAY_RANGE :
				{
					String x = HarveyLanguage.newName();
					String y = HarveyLanguage.newName();
					String z = HarveyLanguage.newName();
					String name = HarveyLanguage.newName();
					HarveyTranslationResult str1 =
						(HarveyTranslationResult) f1.toLang("Harvey", indent);
					HarveyTranslationResult str2 =
						(HarveyTranslationResult) left.toLang("Harvey", indent);
					HarveyTranslationResult str21 =
						HarveyBinaryForm.in(
							new HarveyTranslationResult(y),
							str2);
					HarveyTranslationResult str3 =
						(HarveyTranslationResult) right.toLang(
							"Harvey",
							indent);
					HarveyTranslationResult str31 =
						HarveyBinaryForm.in(
							new HarveyTranslationResult(z),
							str3);
					HarveyTranslationResult str4 =
						HarveyBinaryForm.in(
							new HarveyTranslationResult(x),
							new HarveyTranslationResult(name));

					return new HarveyTranslationResult(
						str1,
						str21,
						str31,
						str4,
						"(forall "
							+ x
							+ " (<-> "
							+ str4.toUniqString()
							+ "(exists "
							+ y
							+ " "
							+ z
							+ " (and "
							+ str21.toUniqString()
							+ " "
							+ str31.toUniqString()
							+ " (= "
							+ x
							+ " (select(select "
							+ str1.toUniqString()
							+ " "
							+ y
							+ ") "
							+ z
							+ "))))))",
						name);
				}
			case Ja_QUESTION :
				{
					String name = HarveyLanguage.newName();
					HarveyTranslationResult str1 =
						(HarveyTranslationResult) f1.toLang("Harvey", indent);
					HarveyTranslationResult str2 =
						(HarveyTranslationResult) left.toLang("Harvey", indent);
					HarveyTranslationResult str3 =
						(HarveyTranslationResult) right.toLang(
							"Harvey",
							indent);

					return new HarveyTranslationResult(
						str1,
						str2,
						str3,
						"(and "
							+ "(-> "
							+ str1.toUniqString()
							+ "(= "
							+ name
							+ " "
							+ str2.toUniqString()
							+ "))"
							+ "(-> (not "
							+ str1.toUniqString()
							+ ") (= "
							+ name
							+ " "
							+ str3.toUniqString()
							+ ")))",
						name);
				}
			default :
				throw new InternalError(
					"HarveyTriaryForm.toLang: case not implemented: "
						+ toString[getNodeType()]);

		}

	}

	HarveyTranslationResult equalsSubsDomToSimmplify(String x, int indent)
		throws LanguageException {
		switch (getNodeType()) {
			case B_ARRAY_EQUALS :
				{
					HarveyTranslationResult str1 =
						(HarveyTranslationResult) getF1().toLang(
							"Harvey",
							indent);
					HarveyTranslationResult str2 =
						(HarveyTranslationResult) getLeft().toLang(
							"Harvey",
							indent);
					HarveyTranslationResult str3 =
						(HarveyTranslationResult) getRight().toLang(
							"Harvey",
							indent);
					return new HarveyTranslationResult(
						str1,
						str2,
						str3,
						"(= (select (select "
							+ str2.toUniqString()
							+ " "
							+ str1.toUniqString()
							+ ") "
							+ x
							+ ") (select (select "
							+ str3.toUniqString()
							+ " "
							+ str1.toUniqString()
							+ ") "
							+ x
							+ "))");
				}
			default :
				throw new InternalError(
					"HarveyTriaryForm.equalsSubsDomToB(String) bad node type: "
						+ right.getNodeType());
		}
	}

}
