//******************************************************************************
/* Copyright (c) 2003 INRIA. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: 
/*
/*******************************************************************************
/* Warnings/Remarks:
/******************************************************************************/

package simplifyPlugin;

import jml2b.exceptions.InternalError;
import jml2b.languages.ITranslatable;
import jml2b.languages.ITranslationResult;
import jml2b.structure.java.Type;

/**
 * @author lburdy
 *
 * To change the template for this generated type comment go to
 * Window&gt;Preferences&gt;Java&gt;Code Generation&gt;Code and Comments
 */
public class SimplifyType extends Type implements ITranslatable {

	/**
	 * 
	 */
	private static final long serialVersionUID = 1L;

	public SimplifyType(Type t) {
		tag = t.getTag();
		refType = t.getRefType();
		elemType = t.getElemType();
	}

	private String getArrayType() {
		switch (tag) {
			case Type.T_BOOLEAN :
				return "c_pd_bool";
			case Type.T_INT :
				return "c_pd_int";
			case Type.T_SHORT :
				return "c_pd_short";
			case Type.T_BYTE :
				return "c_pd_byte";
			case Type.T_CHAR :
				return "c_pd_char";
			case Type.T_LONG :
				return "c_pd_long";
			case Type.T_DOUBLE :
				return "c_pd_double";
			case Type.T_FLOAT :
				return "c_pd_float";
			case Type.T_REF :
				return refType.getBName();
			case Type.T_ARRAY :
			default :
				return new SimplifyType(elemType).getArrayType();
		}
	}

	public ITranslationResult toLang(int indent) {
		switch (tag) {
			case Type.T_BOOLEAN :
				return new SimplifyTranslationResult("BOOL");
			case Type.T_INT :
				return new SimplifyTranslationResult("t_int");
			case Type.T_SHORT :
				return new SimplifyTranslationResult("t_short");
			case Type.T_BYTE :
				return new SimplifyTranslationResult("t_byte");
			case Type.T_CHAR :
				return new SimplifyTranslationResult("t_char");
			case Type.T_LONG :
				return new SimplifyTranslationResult("t_long");
			case Type.T_DOUBLE :
				return new SimplifyTranslationResult("t_double");
			case Type.T_FLOAT :
				return new SimplifyTranslationResult("t_float");
			case Type.T_REF :
				return new SimplifyTranslationResult(
					"(ref " + refType.getBName() + ")");
			case Type.T_ARRAY :
				return new SimplifyTranslationResult(
					"(array "
						+ new SimplifyType(elemType).getArrayType()
						+ " "
						+ getDimension()
						+ ")");
			case Type.T_TYPE :
				return new SimplifyTranslationResult("\\TYPE");
			default :
				throw new InternalError(
					"SimplifyType.toLang() case not handle: " + tag);
		}

	}
}
