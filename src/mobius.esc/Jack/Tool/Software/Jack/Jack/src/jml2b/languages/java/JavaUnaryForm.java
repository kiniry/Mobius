//******************************************************************************
/* Copyright (c) 2003, 2004 INRIA. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: 
/*
/*******************************************************************************
/* Warnings/Remarks:
/******************************************************************************/

package jml2b.languages.java;

import jml2b.exceptions.InternalError;
import jml2b.exceptions.LanguageException;
import jml2b.formula.UnaryForm;
import jml2b.languages.ITranslatable;
import jml2b.languages.ITranslationResult;

/**
 * @author L. Burdy
 */
public class JavaUnaryForm extends UnaryForm implements ITranslatable {

	/**
	 * 
	 */
	private static final long serialVersionUID = 1L;

	JavaUnaryForm(UnaryForm f) {
		super(f);
	}

	/**
	 * Converts the unary formula to a string suitable for output into
	 * the Java view.
	 * <UL>
	 * <li> <code>\old(a)</code> is converted in <code>a</code>
	 * <li> <code>bool(a)</code> is converted in <code>a</code>
	 * <li> <code>{a}</code> is converted in <code>a</code>
	 * <li> <code>!a</code> is converted identically
	 * <li> <code>-a</code> is converted identically
	 * </UL>
	 **/
	public ITranslationResult toLang(int indent) throws LanguageException {
		JavaTranslationResult e =
			(JavaTranslationResult) exp.toLang("Java", indent);
		switch (getNodeType()) {
			case Jm_T_OLD :
			case T_VARIANT_OLD :
				return new JavaTranslationResult(
					"\\old(" + e + ")",
					JavaLanguage.priority[getNodeType()]);

			case Ja_LNOT :
				{
					String es = e.toUniqString();
					if (e.getPriority() < JavaLanguage.priority[getNodeType()])
						es = "(" + es + ")";
					return new JavaTranslationResult(
						"!" + es,
						JavaLanguage.priority[getNodeType()]);
				}
			case Ja_UNARY_NUMERIC_OP :
				String es = e.toUniqString();
				if (e.getPriority() < JavaLanguage.priority[getNodeType()])
					es = "(" + es + ")";
				return new JavaTranslationResult(
					"-" + es,
					JavaLanguage.priority[getNodeType()]);

			case B_BOOL :
				return e;

			case B_ACCOLADE :
				return e;

			case B_DOM :
				return new JavaTranslationResult("dom(" + e + ")", 0);

			case IS_ARRAY :
			case IS_STATIC_FIELD :
				return e;

			default :
				throw new InternalError(
					"JavaUnaryForm.toLang: do not know how to translate "
						+ getNodeType());
		}
	}

}
