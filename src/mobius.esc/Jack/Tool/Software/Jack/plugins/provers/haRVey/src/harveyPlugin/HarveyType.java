//******************************************************************************
/* Copyright (c) 2003, 2004 INRIA. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: 
/*
/*******************************************************************************
/* Warnings/Remarks:
/******************************************************************************/

package harveyPlugin;

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
public class HarveyType extends Type implements ITranslatable {

	/**
	 * 
	 */
	private static final long serialVersionUID = 1L;

	public HarveyType(Type t) {
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
				return new HarveyType(elemType).getArrayType();
		}
	}

	public ITranslationResult toLang(int indent) {
		switch (tag) {
			case Type.T_BOOLEAN :
				return new HarveyTranslationResult("BOOL");
			case Type.T_INT :
				return new HarveyTranslationResult("t_int");
			case Type.T_SHORT :
				return new HarveyTranslationResult("t_short");
			case Type.T_BYTE :
				return new HarveyTranslationResult("t_byte");
			case Type.T_CHAR :
				return new HarveyTranslationResult("t_char");
			case Type.T_LONG :
				return new HarveyTranslationResult("t_long");
			case Type.T_DOUBLE :
				return new HarveyTranslationResult("t_double");
			case Type.T_FLOAT :
				return new HarveyTranslationResult("t_float");
			case Type.T_REF :
				return new HarveyTranslationResult(
					"(ref " + refType.getBName() + ")");
			case Type.T_ARRAY :
				return new HarveyTranslationResult(
					"(array "
						+ new HarveyType(elemType).getArrayType()
						+ " "
						+ getDimension()
						+ ")");
			case Type.T_TYPE :
				return new HarveyTranslationResult("\\TYPE");
			default :
				throw new InternalError(
					"HarveyType.toLang() case not handle: " + tag);
		}

	}
}
