//******************************************************************************
/* Copyright (c) 2003, 2004 INRIA. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: 
/*
/*******************************************************************************
/* Warnings/Remarks:
/******************************************************************************/

package pvsPlugin;

import jml2b.exceptions.TranslationException;
import jml2b.languages.ITranslatable;
import jml2b.languages.ITranslationResult;
import jml2b.structure.java.Type;

/**
 * @author lburdy
 *
 * To change the template for this generated type comment go to
 * Window&gt;Preferences&gt;Java&gt;Code Generation&gt;Code and Comments
 */
public class PvsType extends Type implements ITranslatable {

	/**
	 * 
	 */
	private static final long serialVersionUID = 1L;

	/**
	 * @param type
	 */
	public PvsType(Type t) {
		tag = t.getTag();
		refType = t.getRefType();
		elemType = t.getElemType();
	}

	private String getArrayType() {
		switch (tag) {
			case Type.T_BOOLEAN :
				return "c_bool";
			case Type.T_INT :
				return "c_int";
			case Type.T_SHORT :
				return "c_short";
			case Type.T_BYTE :
				return "c_byte";
			case Type.T_CHAR :
				return "c_char";
			case Type.T_LONG :
				return "c_long";
			case Type.T_DOUBLE :
				return "c_double";
			case Type.T_FLOAT :
				return "c_float";
			case Type.T_REF :
				return refType.getBName();
			case Type.T_ARRAY :
			default :
				return new PvsType(elemType).getArrayType();
		}
	}

	public ITranslationResult toLang(int indent) throws TranslationException {
		switch (tag) {
			case Type.T_BOOLEAN :
				return new PvsTranslationResult("bool");
			case Type.T_INT :
				return new PvsTranslationResult("t_int");
			case Type.T_SHORT :
				return new PvsTranslationResult("t_short");
			case Type.T_BYTE :
				return new PvsTranslationResult("t_byte");
			case Type.T_CHAR :
				return new PvsTranslationResult("t_char");
			case Type.T_REF :
				return new PvsTranslationResult(
					"class(" + refType.getBName() + ")");
			case Type.T_ARRAY :
				return new PvsTranslationResult(
					"arrays( "
						+ new PvsType(elemType).getArrayType()
						+ ","
						+ getDimension()
						+ ")");
			case Type.T_LONG :
				throw new TranslationException("PVS translator: long are not handle.");
			case Type.T_DOUBLE :
				throw new TranslationException("PVS translator: double are not handle.");
			case Type.T_FLOAT :
				throw new TranslationException("PVS translator: float are not handle.");
			case Type.T_TYPE :
				return new PvsTranslationResult("Types");
			default :
				throw new InternalError(
					"PvsType.toLang() case not handle: " + tag);
		}

	}
}
