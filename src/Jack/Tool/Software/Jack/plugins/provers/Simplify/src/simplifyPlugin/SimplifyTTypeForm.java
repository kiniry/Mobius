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
public class SimplifyTTypeForm extends TTypeForm implements ITranslatable {

	/**
	 * 
	 */
	private static final long serialVersionUID = 1L;

	SimplifyTTypeForm(TTypeForm f) {
		super(f);
	}

	public ITranslationResult toLang(int indent) throws LanguageException {
		if (type == null)
			return new SimplifyTranslationResult(nodeText);
		else
			switch (getNodeType()) {
				case Jm_T_TYPE :
					switch (type.getTag()) {
						case Type.T_BOOLEAN :
							return new SimplifyTranslationResult("(ref c_boolean)");
						case Type.T_INT :
							return new SimplifyTranslationResult("(ref c_int)");
						case Type.T_SHORT :
							return new SimplifyTranslationResult("(ref c_short)");
						case Type.T_BYTE :
							return new SimplifyTranslationResult("(ref c_byte)");
						case Type.T_CHAR :
							return new SimplifyTranslationResult("(ref c_char)");
						default :
							return type.toLang("Simplify");
					}
				default :
					return type.toLang("Simplify");
			}
	}
}
