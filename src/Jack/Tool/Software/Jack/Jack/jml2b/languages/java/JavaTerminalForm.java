//******************************************************************************
/* Copyright (c) 2003, 2004 INRIA. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: 
/*
/*******************************************************************************
/* Warnings/Remarks:
/******************************************************************************/

package jml2b.languages.java;

import jml2b.formula.TerminalForm;
import jml2b.languages.ITranslatable;
import jml2b.languages.ITranslationResult;
import jml2b.structure.java.Identifier;

/**
 * @author L. Burdy
 */
public class JavaTerminalForm extends TerminalForm implements ITranslatable {

	/**
	 * 
	 */
	private static final long serialVersionUID = 1L;

	JavaTerminalForm(TerminalForm f) {
		super(f);
	}

	/**
	 * Converts the formula into Java.
	 * @return the Java string corresponding to the formula
	 **/
	public ITranslationResult toLang(int indent) {
		switch (getNodeType()) {
			case Ja_IDENT :
				String res = "";
				if (nodeText != null)
					res = nodeText;
				if (ident != null)
					switch (ident.idType) {
						case Identifier.ID_CLASS :
							res += ident.cl.getName();
							break;
						case Identifier.ID_FIELD :
							if (ident.field.getModifiers() != null
								&& ident.field.getModifiers().isStatic())
								res += ident.field.getDefiningClass().getName()
									+ ".";
							res += ident.field.getName();
							break;
						case Identifier.ID_METHOD :
							res += ident.mth.getName();
							break;
						default :
							throw new jml2b.exceptions.InternalError(
								"display : IDENT : "
									+ ident.idType
									+ " ("
									+ ident.getName()
									+ ")");
					}
				if (postfix)
					res += "an_instance";
				return new JavaTranslationResult(
					res,
					JavaLanguage.priority[getNodeType()]);
			case Ja_LITERAL_false :
				return new JavaTranslationResult(
					"false",
					JavaLanguage.priority[getNodeType()]);
			case Ja_LITERAL_true :
				return new JavaTranslationResult(
					"true",
					JavaLanguage.priority[getNodeType()]);
			case B_BTRUE :
				return new JavaTranslationResult(
					"",
					JavaLanguage.priority[getNodeType()]);
			default :
				return new JavaTranslationResult(
					nodeText,
					JavaLanguage.priority[getNodeType()]);
		}
	}
}
