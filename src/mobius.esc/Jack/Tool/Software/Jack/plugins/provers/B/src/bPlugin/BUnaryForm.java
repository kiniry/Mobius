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
import jml2b.formula.TTypeForm;
import jml2b.formula.UnaryForm;
import jml2b.languages.ITranslatable;
import jml2b.languages.ITranslationResult;

/**
 * @author lburdy
 *
 * To change the template for this generated type comment go to
 * Window&gt;Preferences&gt;Java&gt;Code Generation&gt;Code and Comments
 */
public class BUnaryForm extends UnaryForm implements ITranslatable {

	static final long serialVersionUID = 8296832951677711019L;
	String lang;

	BUnaryForm(String lang, UnaryForm f) {
		super(f);
		this.lang = lang;
	}

	/**
	 * Converts the unary formula to a string into the B language.
	 * <UL>
	 * <li> <code>\old(a)</code> is converted in <code>a</code>
	 * <li> <code>!a</code> is converted in <code>not(a)</code>
	 * <li> <code>bool(a)</code> is converted identically
	 * <li> <code>{a}</code> is converted identically
	 * <li> <code>-a</code> is converted identically
	 * </UL>
	 **/
	public ITranslationResult toLang(int indent) throws LanguageException {
		switch (getNodeType()) {
			case IS_ARRAY :
				if (exp instanceof TTypeForm)
					return new BTranslationResult(
						BPrinter.arrayDecl(
							((TTypeForm) exp).getTag()));
				else
					return new BTranslationResult(
						BPrinter.arrayRefDecl(
							exp.toLang(lang, indent).toUniqString()));
			case IS_STATIC_FIELD :
			case Jm_T_OLD :
				return exp.toLang(lang, indent);
			case Ja_LNOT :
				return new BTranslationResult(
					"not(" + exp.toLang(lang, indent).toUniqString() + ")");
			case Ja_UNARY_NUMERIC_OP :
				String res;
				if (BLanguage.priority[exp.getNodeType()]
					< BLanguage.priority[getNodeType()])
					res = "(" + exp.toLang(lang, indent).toUniqString() + ")";
				else
					res = exp.toLang(lang, indent).toUniqString();
				return new BTranslationResult("- " + res);
			case B_BOOL :
				return new BTranslationResult(
					"bool(" + exp.toLang(lang, indent).toUniqString() + ")");
			case B_ACCOLADE :
				return new BTranslationResult(
					"{" + exp.toLang(lang, indent).toUniqString() + "}");
			case B_DOM :
				return new BTranslationResult(
					"dom(" + exp.toLang(lang, indent).toUniqString() + ")");
			default :
				throw new InternalError(
					"BUnaryForm.toLang() bad node type:" + getNodeType());
		}
	}

}
