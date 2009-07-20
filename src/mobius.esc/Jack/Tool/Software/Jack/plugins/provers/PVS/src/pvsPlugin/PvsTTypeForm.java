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
public class PvsTTypeForm extends TTypeForm implements ITranslatable {

	/**
	 * 
	 */
	private static final long serialVersionUID = 1L;

	/**
	 * @param form
	 */
	public PvsTTypeForm(TTypeForm form) {
		super(form);
	}

	public ITranslationResult toLang(int indent) throws LanguageException {
		if (type == null)
			return new PvsTranslationResult(nodeText);
		else
		switch (getNodeType()) {
			case Jm_T_TYPE :
				switch (type.getTag()) {
					case Type.T_BOOLEAN :
						return new PvsTranslationResult("class(c_boolean)");
					case Type.T_INT :
						return new PvsTranslationResult("class(c_int)");
					case Type.T_SHORT :
						return new PvsTranslationResult("class(c_short)");
					case Type.T_BYTE :
						return new PvsTranslationResult("class(c_byte)");
					case Type.T_CHAR :
						return new PvsTranslationResult("class(c_char)");
					default :
						return type.toLang("PVS");
				}
			default :
				return type.toLang("PVS");
		}
	}
}
