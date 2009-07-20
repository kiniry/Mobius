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
import jml2b.formula.TriaryForm;
import jml2b.languages.ITranslatable;
import jml2b.languages.ITranslationResult;
import jml2b.structure.statement.Statement;

/**
 * @author lburdy
 *
 * To change the template for this generated type comment go to
 * Window&gt;Preferences&gt;Java&gt;Code Generation&gt;Code and Comments
 */
public class BTriaryForm extends TriaryForm implements ITranslatable {

	static final long serialVersionUID = -3497684142321437240L;
	String lang;

	BTriaryForm(String lang, TriaryForm f) {
		super(f);
		this.lang = lang;
	}

	/**
	 * Converts the current formula to a string suitable for output to
	 * the Atelier B.
	 * @return
	 * <UL>
	 * <li> <code>({TRUE |-> left} <+ {FALSE |-> right})(bool(f1))</code>
	 * <li> <code>f1 <| left = f1 <| right</code>
	 * </UL>
	 **/
	public ITranslationResult toLang(int indent) throws LanguageException {
		switch (getNodeType()) {
			case B_ARRAY_EQUALS :
				return new BTranslationResult(
					left.toLang(lang, indent).toUniqString()
						+ "("
						+ f1.toLang(lang, indent).toUniqString()
						+ ") = "
						+ right.toLang(lang, indent).toUniqString()
						+ "("
						+ f1.toLang(lang, indent).toUniqString()
						+ ")");
			case NEW_OBJECT :
				return new BTranslationResult(
					left.toLang(lang, indent).toUniqString()
						+ " = {"
						+ f1.toLang(lang, indent).toUniqString()
						+ "} <<| "
						+ right.toLang(lang, indent).toUniqString()
						+ " & "
						+ f1.toLang(lang, indent).toUniqString()
						+ ": dom("
						+ right.toLang(lang, indent).toUniqString()
						+ ")");
			case ARRAY_RANGE :
				String x = Statement.fresh();
				return new BTranslationResult(
					"UNION("
						+ x
						+ ").("
						+ x
						+ ": "
						+ left.toLang(lang, indent).toUniqString()
						+ " | "
						+ f1.toLang(lang, indent).toUniqString()
						+ "("
						+ x
						+ ")["
						+ right.toLang(lang, indent).toUniqString()
						+ "])");

			case Ja_QUESTION :
				return new BTranslationResult(
					"({TRUE |-> "
						+ left.toLang(lang, indent).toUniqString()
						+ " } <+ { FALSE |-> "
						+ right.toLang(lang, indent).toUniqString()
						+ " })(bool("
						+ f1.toLang(lang, indent).toUniqString()
						+ "))");
			case CONSTANT_FUNCTION_FUNCTION :
				String res = "";
				if (BLanguage.priority[f1.getNodeType()]
					< BLanguage.priority[getNodeType()]) {
					res = "(" + f1.toLang(lang, indent).toUniqString() + ")";
				} else
					res = f1.toLang(lang, indent).toUniqString();

				return new BTranslationResult(
					res
						+ " * {"
						+ left.toLang(lang, indent).toUniqString()
						+ " * {"
						+ right.toLang(lang, indent).toUniqString()
						+ "}}");
				//			case EQUAL_SUBSTRACTION_DOM :
				//				return new BTranslationResult(
				//					"dom("
				//						+ left.toLang(lang, indent).toUniqString()
				//						+ ") = dom("
				//						+ right.toLang(lang, indent).toUniqString()
				//						+ ") & "
				//						+ f1.toLang(lang, indent).toUniqString()
				//						+ "<<|"
				//						+ left.toLang(lang, indent).toUniqString()
				//						+ " = "
				//						+ f1.toLang(lang, indent).toUniqString()
				//						+ "<<|"
				//						+ right.toLang(lang, indent).toUniqString());
			default :
				throw new InternalError(
					"BTriaryForm.toLang() bad node type:" + getNodeType());
		}
	}

	ITranslationResult equalsSubsDomToB(String subs, int indent)
		throws LanguageException {
		switch (getNodeType()) {
			case B_ARRAY_EQUALS :
				{
					String p = f1.toLang(lang, indent).toUniqString();
					String l = left.toLang(lang, indent).toUniqString();
					String r = right.toLang(lang, indent).toUniqString();
					return new BTranslationResult(
						"dom("
							+ l
							+ "("
							+ p
							+ ")) = dom("
							+ r
							+ "("
							+ p
							+ ")) &"
							+ subs
							+ " <<| "
							+ l
							+ "("
							+ p
							+ ") = "
							+ subs
							+ " <<| "
							+ r
							+ "("
							+ p
							+ ")");
				}
			default :
				throw new InternalError(
					"TriaryForm.equalsSubsDomToB(String) bad node type: "
						+ getNodeType());
		}
	}

}
