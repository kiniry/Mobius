//******************************************************************************
/* Copyright (c) 2003, 2004 INRIA. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: 
/*
/*******************************************************************************
/* Warnings/Remarks:
/******************************************************************************/

package coqPlugin.language;

import jml2b.exceptions.LanguageException;
import jml2b.exceptions.TranslationException;
import jml2b.formula.BinaryForm;
import jml2b.formula.Formula;
import jml2b.formula.TerminalForm;
import jml2b.formula.UnaryForm;
import jml2b.languages.ITranslatable;
import jml2b.languages.ITranslationResult;
import jml2b.structure.java.Identifier;
import coqPlugin.CoqTranslationResult;

/**
 * @author lburdy
 *
 * To change the template for this generated type comment go to
 * Window&gt;Preferences&gt;Java&gt;Code Generation&gt;Code and Comments
 */
public class CoqUnaryForm extends UnaryForm implements ITranslatable {

	/**
	 * 
	 */
	private static final long serialVersionUID = 1L;
	/**
	 * @param form
	 */
	public CoqUnaryForm(UnaryForm form) {
		super(form);
	}

	public ITranslationResult toLang(int indent) throws LanguageException {
		
		CoqTranslationResult ctr =
			(CoqTranslationResult) exp.toLang("Coq", indent);
		if(exp == this) {
			throw new TranslationException(
					"CoqUnaryForm.toLang: I am the same as myself.");
		}
		CoqType type = CoqType.basicType(exp.getBasicType());
		switch (getNodeType()) {
			case B_BOOL :
			return new CoqTranslationResult(
				ctr,
				"(" + ctr.getFunPart() + ")");
			case Jm_T_OLD :
				return ctr;
			case Ja_LNOT :
				return new CoqTranslationResult(
					ctr,
					"(not (" + ctr.getFunPart() + "))");
			case Ja_UNARY_NUMERIC_OP :
				return new CoqTranslationResult(
					ctr,
					"(j_mul (j_neg 1) " + ctr.getFunPart() + ")");
			case B_ACCOLADE :
				return new CoqTranslationResult(
					ctr,
					"(singleton (" + type + ") " + ctr.getFunPart() + ")");
			case B_DOM :
				return dom(exp);
			case IS_ARRAY:
				return new CoqTranslationResult(ctr, CoqType.Reference + " ->" + ctr);
			default :
				throw new TranslationException(
					"CoqUnaryForm.toLang: "
						+ "default case should not be reached "
						+ getNodeType());
		}

	}
	CoqTranslationResult dom(Formula exp) throws TranslationException {
		switch (exp.getNodeType()) {
			case B_COUPLE :
				{
					CoqTranslationResult ptr1 =
						dom(((BinaryForm) exp).getLeft());
					return new CoqTranslationResult(
						ptr1,
						"(" + ptr1 + " = true)");
				}
			case B_OVERRIDING :
				// TODO: Make it work 
				CoqTranslationResult ptr1 = dom(((BinaryForm) exp).getLeft());
				CoqTranslationResult ptr2 = dom(((BinaryForm) exp).getRight());
				return new CoqTranslationResult( ptr1, ptr2, ptr1 + " WITH " + ptr2);
				
			case Jm_T_OLD :
				return dom(((UnaryForm) exp).getExp());
			case Ja_IDENT :
				String txt = ((TerminalForm) exp).getNodeText();
				if (txt.indexOf("intelements") == 0)
					return new CoqTranslationResult(
						"(fun (x: "+ CoqType.Reference + ") =>"
							+ " (instances x) /\\ typeof(x) = (array (class c_int) 1))");
				if (txt.indexOf("shortelements") == 0)
					return new CoqTranslationResult(
						"(fun (x: "+ CoqType.Reference + ") =>"
							+ " (instances x) /\\ typeof(x) = (array (class c_short) 1))");
				if (txt.indexOf("byteelements") == 0)
					return new CoqTranslationResult(
						"(fun (x: "+ CoqType.Reference + ") =>"
							+ " (instances x) /\\ typeof(x) = (array (class c_byte) 1))");
				if (txt.indexOf("charelements") == 0)
					return new CoqTranslationResult(
						"(fun (x: "+ CoqType.Reference + ") =>"
							+ " (instances x) /\\ typeof(x) = (array (class c_char) 1))");
				if (txt.indexOf("booleanelements") == 0)
					return new CoqTranslationResult(
						"(fun (x: "+ CoqType.Reference + ") =>"
							+ " (instances x) /\\ typeof(x) = (array (class c_boolean) 1))");
				if (txt.indexOf("refelements") == 0)
					return new CoqTranslationResult(
							"(fun (x: "+ CoqType.Reference + ") =>"
							+ "(instances x) /\\  (elemtypeDomDef (typeof x)) /\\ "
							+ "typeof x <> array (class c_int) 1 :>Types /\\ "
							+ "typeof x <> array (class c_short) 1 :>Types /\\ "
							+ "typeof x <> array (class c_byte) 1 :>Types /\\ "
							+ "typeof x <> array (class c_char) 1 :>Types)");
				Identifier ident = ((TerminalForm) exp).getIdent();
				if (ident != null) {
					return new CoqTranslationResult(
							"(fun (x: "+ CoqType.Reference + ") =>"
							+ "(instances x) /\\  (elemtypeDomDef (typeof x)"
							//+ ident.field.getDefiningClass().getBName()
							+ ") /\\ "
							+ "typeof x <> array (class c_int) 1 :>Types /\\ "
							+ "typeof x <> array (class c_short) 1 :>Types /\\ "
							+ "typeof x <> array (class c_byte) 1 :>Types /\\ "
							+ "typeof x <> array (class c_char) 1 :>Types)");
				}
				throw new TranslationException(
					"CoqUnaryForm.toLang B_DOM Ja_IDENT: "
						+ "default case should not be reached "
						+ txt);
			default :
				throw new TranslationException(
					"CoqUnaryForm.toLang B_DOM: "
						+ "default case should not be reached "
						+ exp.getNodeType());
		}
	}

}
