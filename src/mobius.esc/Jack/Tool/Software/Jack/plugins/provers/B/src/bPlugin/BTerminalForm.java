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
public class BTerminalForm extends TerminalForm implements ITranslatable {

	static final long serialVersionUID = 1763601890211987599L;

	BTerminalForm(TerminalForm f) {
		super(f);
	}

	public ITranslationResult toLang(int indent) {
		switch (getNodeType()) {
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
								return new BTranslationResult(
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
				return new BTranslationResult(res);
			case Ja_LITERAL_false :
				return new BTranslationResult("FALSE");
			case Ja_LITERAL_true :
				return new BTranslationResult("TRUE");
			case Ja_STRING_LITERAL :
				return new BTranslationResult(
					"j_string(" + getNodeText() + ")");
			case Jm_T_RESULT :
				return new BTranslationResult("result");
			default :
				return new BTranslationResult(getNodeText());
		}
	}
}
