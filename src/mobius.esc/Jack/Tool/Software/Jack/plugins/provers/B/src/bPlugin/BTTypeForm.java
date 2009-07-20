//******************************************************************************
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
import jml2b.languages.ITranslatable;
import jml2b.languages.ITranslationResult;
import jml2b.structure.java.Type;

/**
 * @author lburdy
 *
 * To change the template for this generated type comment go to
 * Window&gt;Preferences&gt;Java&gt;Code Generation&gt;Code and Comments
 */
public class BTTypeForm extends TTypeForm implements ITranslatable {

	static final long serialVersionUID = -6892853046993712276L;
	String lang;

	BTTypeForm(String lang, TTypeForm f) {
		super(f);
		this.lang = lang;
	}

	public ITranslationResult toLang(int indent) throws LanguageException {
		if (type == null)
			return new BTranslationResult(nodeText);
		else
			switch (getNodeType()) {
				case Jm_T_TYPE :
					switch (type.getTag()) {
						case Type.T_BOOLEAN :
							return new BTranslationResult(BPrinter.c_boolean);
						case Type.T_INT :
							return new BTranslationResult(BPrinter.c_int);
						case Type.T_SHORT :
							return new BTranslationResult(BPrinter.c_short);
						case Type.T_BYTE :
							return new BTranslationResult(BPrinter.c_byte);
						case Type.T_CHAR :
							return new BTranslationResult(BPrinter.c_char);
						default :
							return type.toLang(lang);
					}
				default :
					return type.toLang(lang);
			}
	}

}
