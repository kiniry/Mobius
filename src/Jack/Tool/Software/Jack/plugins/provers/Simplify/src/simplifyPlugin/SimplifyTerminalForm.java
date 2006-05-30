//******************************************************************************
/* Copyright (c) 2003 INRIA. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: 
/*
/*******************************************************************************
/* Warnings/Remarks:
/******************************************************************************/

package simplifyPlugin;

import jml2b.exceptions.LanguageException;
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
public class SimplifyTerminalForm extends TerminalForm implements ITranslatable {

	/**
	 * 
	 */
	private static final long serialVersionUID = 1L;

	SimplifyTerminalForm(TerminalForm f) {
		super(f);
	}

	public ITranslationResult toLang(int indent) throws LanguageException {
		switch (getNodeType()) {
			case B_BTRUE :
				return new SimplifyTranslationResult("TRUE");
			case Ja_LITERAL_false :
				return new SimplifyTranslationResult("|@false|");
			case Ja_LITERAL_true :
				return new SimplifyTranslationResult("|@true|");
			case Ja_STRING_LITERAL :
				return new SimplifyTranslationResult(
					"(j_string |" + getNodeText().replace('|', ' ') + "|)");
			case Ja_IDENT :
				String res = "";
				if (getNodeText() != null)
					res = getNodeText();
				if (ident != null)
					switch (ident.idType) {
						case Identifier.ID_CLASS :
							res += ident.cl.getBName();
							break;
						case Identifier.ID_FIELD :
							if (ident.field.isExpanded())
								return new SimplifyTranslationResult(
									Integer.toString(
										ident.field.getAssign().getValue()));
							res += ident.field.getBName();
							break;
						case Identifier.ID_METHOD :
							res += ident.mth.getBName();
							break;
						default :
							throw new jml2b.exceptions.InternalError(
								"TerminalForm.toB(): IDENT: "
									+ ident.getName()
									+ " with idType: "
									+ ident.idType);
					}
				if (postfix)
					res += "an_instance";
				return new SimplifyTranslationResult("|" + res + "|");
			case Ja_NUM_INT :
				return new SimplifyTranslationResult(getNodeText());
			case Jm_T_RESULT :
				return new SimplifyTranslationResult("result");
			case FINAL_IDENT :
			case Ja_CHAR_LITERAL :
			case Ja_JAVA_BUILTIN_TYPE :
			case Ja_LITERAL_null :
			case Ja_LITERAL_this :
			case Ja_LITERAL_super :
			default :
				return new SimplifyTranslationResult("|" + getNodeText() + "|");
		}
	}
}
