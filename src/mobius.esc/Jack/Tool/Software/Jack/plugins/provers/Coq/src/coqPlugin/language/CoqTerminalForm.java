//******************************************************************************
/* Copyright (c) 2003, 2004 INRIA. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: 
/*
/*******************************************************************************
/* Warnings/Remarks:
/******************************************************************************/

package coqPlugin.language;

import coqPlugin.CoqTranslationResult;
import jml2b.exceptions.LanguageException;
import jml2b.exceptions.TranslationException;
import jml2b.formula.IFormToken;
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
public class CoqTerminalForm extends CoqFormula implements ITranslatable, IFormToken {

	public final static CoqTranslationResult $null = new CoqTranslationResult("null");
	public final static CoqTranslationResult $true = new CoqTranslationResult("true");
	public final static CoqTranslationResult $false = new CoqTranslationResult("false");
	
	/**
	 * 
	 */
	private static final long serialVersionUID = 1L;

	/**
	 * @param form
	 */
	private final String text;
	private final Identifier ident;
	private final boolean postfix;
	
	public CoqTerminalForm(TerminalForm form) {
		super(form.getNodeType());
		ident = form.getIdent();
		text = form.getNodeText();
		postfix = form.isPostfix();		
	}

	public ITranslationResult toLang(int indent) throws LanguageException {
		switch (nodetype) {
			case Ja_IDENT :
				String res = "";
				
				if (text != null) {
	
					res = text;
//					Logger.get().println(res);
				}
				
				if (ident != null)
					switch (ident.idType) {
						case Identifier.ID_CLASS :
							res += ident.cl.getBName();
//							Logger.get().println(res);
							break;
						case Identifier.ID_FIELD :
							// the case for field and local variable translation.
							if (ident.field.isExpanded())
								return new CoqTranslationResult(
									Integer.toString(
											ident.field.getAssign().getValue())
										);
							String name = ident.field.getBName();
							CoqVar.putName(name);
							res += CoqVar.getCoqName(name);
							break;
						case Identifier.ID_METHOD :
							res += ident.mth.getBName();
//							Logger.get().println(res);
							break;
						default :
							throw new jml2b.exceptions.InternalError(
								"TerminalForm.toCoq(): IDENT: "
									+ ident.getName()
									+ " with idType: "
									+ ident.idType);
					}
				if (postfix) {
					res += "_an_instance";
				}
				if (text.startsWith("arraylength"))
					return new CoqTranslationResult("arraylength");
				//Logger.get().println(res);
				return new CoqTranslationResult(res);
			case B_BTRUE :
				return new CoqTranslationResult("(* 0 = 0 *)True");
			case Ja_LITERAL_false :
				return $false;
			case Ja_LITERAL_true :
				return $true;
			case Ja_STRING_LITERAL :
				return $null;
				//TODO: String translation?
				//throw new TranslationException("Coq Translator: Strings are not handle");
			case Ja_NUM_INT :
				String str = text;
				if(str.charAt(0) == '-') {
					str = "(j_neg" +str.replace('-', ' ') + ")";
				}
				return new CoqTranslationResult(str);
			case FINAL_IDENT :
				if (text.startsWith("arraylength"))
					return new CoqTranslationResult("arraylength");
			case Ja_LITERAL_null :
			case Ja_LITERAL_this :
			case Ja_LITERAL_super :
				String name = text;
				CoqVar.putName(name);
				name = CoqVar.getCoqName(name);
				return new CoqTranslationResult(name);
			case Jm_T_RESULT :
				return new CoqTranslationResult("result");
				//			case MODIFIED_FIELD :
				//				return new CoqTranslationResult(
				//					getNodeText(),
				//					new VType(ident.field));
			case Ja_CHAR_LITERAL :
			case Ja_JAVA_BUILTIN_TYPE :
			default :
				throw new TranslationException(
					"CoqTerminalForm.toLang " + nodetype);
		}
	}
}
