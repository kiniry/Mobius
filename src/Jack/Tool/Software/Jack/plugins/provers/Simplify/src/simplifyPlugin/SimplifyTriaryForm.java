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
import jml2b.formula.BasicType;
import jml2b.formula.TriaryForm;
import jml2b.languages.ITranslatable;
import jml2b.languages.ITranslationResult;

/**
 * @author lburdy
 *
 * To change the template for this generated type comment go to
 * Window&gt;Preferences&gt;Java&gt;Code Generation&gt;Code and Comments
 */
public class SimplifyTriaryForm extends TriaryForm implements ITranslatable {

	/**
	 * 
	 */
	private static final long serialVersionUID = 1L;

	SimplifyTriaryForm(TriaryForm f) {
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
					String x = SimplifyLanguage.newName();

					SimplifyTranslationResult str1 =
						equalsSubsDomToSimmplify(x, indent);
					return new SimplifyTranslationResult(
						str1,
						"(FORALL (" + x + ") " + str1.toUniqString() + ")");
				}
			case NEW_OBJECT :
				{
					String x = SimplifyLanguage.newName();
					SimplifyTranslationResult str1 =
						(SimplifyTranslationResult) f1.toLang(
							"Simplify",
							indent);
					SimplifyTranslationResult str2 =
						(SimplifyTranslationResult) left.toLang(
							"Simplify",
							indent);
					SimplifyTranslationResult str3 =
						(SimplifyTranslationResult) right.toLang(
							"Simplify",
							indent);
					return new SimplifyTranslationResult(
						str1,
						str2,
						str3,
						"(FORALL ("
							+ x
							+ ") (IMPLIES (NEQ"
							+ x
							+ " "
							+ str1.toUniqString()
							+ ")"
							+ "(EQ (select "
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
					String x = SimplifyLanguage.newName();
					String y = SimplifyLanguage.newName();
					String z = SimplifyLanguage.newName();
					String name = SimplifyLanguage.newName();
					SimplifyTranslationResult str1 =
						(SimplifyTranslationResult) f1.toLang(
							"Simplify",
							indent);
					SimplifyTranslationResult str2 =
						(SimplifyTranslationResult) left.toLang(
							"Simplify",
							indent);
					SimplifyTranslationResult str21 =
						SimplifyBinaryForm.in(
							new SimplifyTranslationResult(y),
							str2);
					SimplifyTranslationResult str3 =
						(SimplifyTranslationResult) right.toLang(
							"Simplify",
							indent);
					SimplifyTranslationResult str31 =
						SimplifyBinaryForm.in(
							new SimplifyTranslationResult(z),
							str3);
					SimplifyTranslationResult str4 =
						SimplifyBinaryForm.in(
							new SimplifyTranslationResult(x),
							new SimplifyTranslationResult(name));

					return new SimplifyTranslationResult(
						str1,
						str21,
						str31,
						str4,
						"(FORALL ("
							+ x
							+ ") (IFF "
							+ str4.toUniqString()
							+ "(EXISTS ("
							+ y
							+ " "
							+ z
							+ ") (AND "
							+ str21.toUniqString()
							+ " "
							+ str31.toUniqString()
							+ " (EQ "
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
					String name = SimplifyLanguage.newName();
					SimplifyTranslationResult str1 =
						(SimplifyTranslationResult) f1.toLang(
							"Simplify",
							indent);
					SimplifyTranslationResult str2 =
						(SimplifyTranslationResult) left.toLang(
							"Simplify",
							indent);
					SimplifyTranslationResult str3 =
						(SimplifyTranslationResult) right.toLang(
							"Simplify",
							indent);
					if (left.getBasicType() == BasicType.PropType)
						return new SimplifyTranslationResult(
							str1,
							str2,
							str3,
							"(AND "
								+ "(IMPLIES "
								+ str1.toUniqString()
								+ "(IFF "
								+ name
								+ " "
								+ str2.toUniqString()
								+ "))"
								+ "(IMPLIES (NOT "
								+ str1.toUniqString()
								+ ") (IFF "
								+ name
								+ " "
								+ str3.toUniqString()
								+ ")))",
							name);
					else
						return new SimplifyTranslationResult(
							str1,
							str2,
							str3,
							"(AND "
								+ "(IMPLIES "
								+ str1.toUniqString()
								+ "(EQ "
								+ name
								+ " "
								+ str2.toUniqString()
								+ "))"
								+ "(IMPLIES (NOT "
								+ str1.toUniqString()
								+ ") (EQ "
								+ name
								+ " "
								+ str3.toUniqString()
								+ ")))",
							name);
				}
			default :
				throw new InternalError(
					"SimplifyTriaryForm.toLang: case not implemented: "
						+ toString[getNodeType()]);

		}

	}

	SimplifyTranslationResult equalsSubsDomToSimmplify(String x, int indent)
		throws LanguageException {
		switch (getNodeType()) {
			case B_ARRAY_EQUALS :
				{
					SimplifyTranslationResult str1 =
						(SimplifyTranslationResult) getF1().toLang(
							"Simplify",
							indent);
					SimplifyTranslationResult str2 =
						(SimplifyTranslationResult) getLeft().toLang(
							"Simplify",
							indent);
					SimplifyTranslationResult str3 =
						(SimplifyTranslationResult) getRight().toLang(
							"Simplify",
							indent);
					return new SimplifyTranslationResult(
						str2,
						str3,
						"(EQ (select (select "
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
					"BinaryForm.equalsSubsDomToB(String) bad node type: "
						+ right.getNodeType());
		}
	}

}
