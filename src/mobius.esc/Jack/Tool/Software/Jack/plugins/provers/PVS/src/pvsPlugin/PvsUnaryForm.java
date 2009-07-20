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
import jml2b.exceptions.TranslationException;
import jml2b.formula.BinaryForm;
import jml2b.formula.Formula;
import jml2b.formula.TTypeForm;
import jml2b.formula.TerminalForm;
import jml2b.formula.UnaryForm;
import jml2b.languages.ITranslatable;
import jml2b.languages.ITranslationResult;
import jml2b.structure.java.Identifier;
import jml2b.structure.java.Type;

/**
 * @author lburdy
 *
 * To change the template for this generated type comment go to
 * Window&gt;Preferences&gt;Java&gt;Code Generation&gt;Code and Comments
 */
public class PvsUnaryForm extends UnaryForm implements ITranslatable {

	/**
	 * 
	 */
	private static final long serialVersionUID = 1L;

	/**
	 * @param form
	 */
	public PvsUnaryForm(UnaryForm form) {
		super(form);
	}

	public ITranslationResult toLang(int indent) throws LanguageException {
		PvsTranslationResult str =
			(PvsTranslationResult) exp.toLang("PVS", indent);
		switch (getNodeType()) {
			case IS_ARRAY :
				if (exp instanceof TTypeForm) {
					return new PvsTranslationResult(
						PvsPrinter.arrayType(
							((TTypeForm) exp).getTag()));
				} else
					return new PvsTranslationResult(
						PvsPrinter.arrayType(Type.T_REF));
			case B_BOOL :
			case Jm_T_OLD :
			case IS_STATIC_FIELD :
				return str;
			case Ja_LNOT :
				return new PvsTranslationResult("NOT " + str.toUniqString());
			case Ja_UNARY_NUMERIC_OP :
				return new PvsTranslationResult("- " + str.toUniqString());
			case B_ACCOLADE :
				return new PvsTranslationResult(
					"(LAMBDA (x:"
						+ PvsLanguage.basicType(exp.getBasicType())
						+ "): x = "
						+ str.toUniqString()
						+ ")");
			case B_DOM :
				return dom(exp);

			default :
				throw new TranslationException(
					"PvsUnaryForm.toLang: "
						+ "default case should not be reached "
						+ getNodeType());
		}

	}

	PvsTranslationResult dom(Formula exp) throws TranslationException {
		switch (exp.getNodeType()) {
			case B_COUPLE :
				{
					PvsTranslationResult ptr1 =
						dom(((BinaryForm) exp).getLeft());
					return new PvsTranslationResult(
						ptr1,
						"[" + ptr1.toUniqString() + " := true]");
				}
			case B_OVERRIDING :
				PvsTranslationResult ptr1 = dom(((BinaryForm) exp).getLeft());
				PvsTranslationResult ptr2 = dom(((BinaryForm) exp).getRight());
				return new PvsTranslationResult(
					ptr1,
					ptr2,
					ptr1.toUniqString() + " WITH " + ptr2.toUniqString());
			case Jm_T_OLD :
				return dom(((UnaryForm) exp).getExp());
			case Ja_IDENT :
				String txt = ((TerminalForm) exp).getNodeText();
				if (txt.indexOf("intelements") == 0)
					return new PvsTranslationResult(
						"(LAMBDA (x: REFERENCES) :"
							+ " instances?(x) AND typeof(x) = arrays(c_int, 1))");
				if (txt.indexOf("shortelements") == 0)
					return new PvsTranslationResult(
						"(LAMBDA (x: REFERENCES) :"
							+ " instances?(x) AND typeof(x) = arrays(c_short, 1))");
				if (txt.indexOf("byteelements") == 0)
					return new PvsTranslationResult(
						"(LAMBDA (x: REFERENCES) :"
							+ " instances?(x) AND typeof(x) = arrays(c_byte, 1))");
				if (txt.indexOf("charelements") == 0)
					return new PvsTranslationResult(
						"(LAMBDA (x: REFERENCES) :"
							+ " instances?(x) AND typeof(x) = arrays(c_char, 1))");
				if (txt.indexOf("booleanelements") == 0)
					return new PvsTranslationResult(
						"(LAMBDA (x: REFERENCES) :"
							+ " instances?(x) AND typeof(x) = arrays(c_boolean, 1))");
				if (txt.indexOf("refelements") == 0)
					return new PvsTranslationResult(
						"(LAMBDA (x: REFERENCES) :"
							+ " instances?(x) AND arrays?(typeof(x)))");
				Identifier ident = ((TerminalForm) exp).getIdent();
				if (ident != null) {
					return new PvsTranslationResult(
						"(LAMBDA (x: REFERENCES) :"
							+ "instances?(x) AND  typeof(x) = class("
							+ ident.field.getDefiningClass().getBName()
							+ "))");
				}
				throw new TranslationException(
					"PvsUnaryForm.toLang B_DOM Ja_IDENT: "
						+ "default case should not be reached "
						+ txt);
			default :
				throw new TranslationException(
					"PvsUnaryForm.toLang B_DOM: "
						+ "default case should not be reached "
						+ exp.getNodeType());
		}
	}

}
