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
import jml2b.formula.TerminalForm;
import jml2b.languages.ITranslatable;
import jml2b.languages.ITranslationResult;
import jml2b.structure.java.Identifier;

/**
 * @author lburdy
 *
 * To change the template for this generated type comment go to
 * Window&gt;Preferences&gt;Java&gt;Code Generation&gt;Code and Comments
 */
public class PvsTerminalForm extends TerminalForm implements ITranslatable {

	/**
	 * 
	 */
	private static final long serialVersionUID = 1L;

	/**
	 * @param form
	 */
	public PvsTerminalForm(TerminalForm form) {
		super(form);
	}

	public ITranslationResult toLang(int indent) throws LanguageException {
		switch (getNodeType()) {
			case Ja_IDENT :
				String res = "";
				if (getNodeText() != null)
					res = getNodeText();
				if (res.equals("instances"))
					res = res + "?";
				if (ident != null)
					switch (ident.idType) {
						case Identifier.ID_CLASS :
							res += ident.cl.getBName();
							break;
						case Identifier.ID_FIELD :
							if (ident.field.isExpanded())
								return new PvsTranslationResult(
									Integer.toString(
										ident.field.getAssign().getValue()));
							res += ident.field.getBName();
							break;
						case Identifier.ID_METHOD :
							res += ident.mth.getBName();
							break;
						default :
							throw new jml2b.exceptions.InternalError(
								"PvsTerminalForm.toLang(): IDENT: "
									+ ident.getName()
									+ " with idType: "
									+ ident.idType);
					}
				if (postfix) {
					res += "an_instance";
				}
				return new PvsTranslationResult(res);
			case B_BTRUE :
				return new PvsTranslationResult("true");
			case Ja_LITERAL_false :
				return new PvsTranslationResult("false");
			case Ja_LITERAL_true :
				return new PvsTranslationResult("true");
			case Ja_STRING_LITERAL :
				throw new TranslationException("PVS Translator: Strings are not handle");
			case Ja_NUM_INT :
			case FINAL_IDENT :
			case Ja_LITERAL_null :
			case Ja_LITERAL_this :
			case Ja_LITERAL_super :
				return new PvsTranslationResult(getNodeText());
			case Jm_T_RESULT :
				return new PvsTranslationResult("result");
				//			case MODIFIED_FIELD :
				//				return new CoqTranslationResult(
				//					getNodeText(),
				//					new VType(ident.field));
			case Ja_CHAR_LITERAL :
			case Ja_JAVA_BUILTIN_TYPE :
			default :
				throw new TranslationException(
					"PvsTerminalForm.toLang " + getNodeType());
		}
	}
}
