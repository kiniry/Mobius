//******************************************************************************
/* Copyright (c) 2003, 2004 INRIA. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: 
/*
/*******************************************************************************
/* Warnings/Remarks:
/******************************************************************************/

package jml2b.languages.java;

import jml2b.exceptions.LanguageException;
import jml2b.languages.ITranslatable;
import jml2b.languages.ITranslationResult;
import jml2b.structure.java.Type;

/**
 * @author L. Burdy
 */
public class JavaType extends Type implements ITranslatable {

	/**
	 * 
	 */
	private static final long serialVersionUID = 1L;

	JavaType(Type t) {
		tag = t.getTag();
		refType = t.getRefType();
		elemType = t.getElemType();
	}

	public ITranslationResult toLang(int indent) throws LanguageException {
		switch (getTag()) {
			case jml2b.structure.java.Type.T_INT :
				return new JavaTranslationResult("int",0);
			case jml2b.structure.java.Type.T_SHORT :
				return new JavaTranslationResult("short",0);
			case jml2b.structure.java.Type.T_BYTE :
				return new JavaTranslationResult("byte",0);
			case jml2b.structure.java.Type.T_BOOLEAN :
				return new JavaTranslationResult("boolean",0);
			case jml2b.structure.java.Type.T_CHAR :
				return new JavaTranslationResult("char",0);
			case jml2b.structure.java.Type.T_VOID :
				return new JavaTranslationResult("void",0);
			case jml2b.structure.java.Type.T_LONG :
				return new JavaTranslationResult("long",0);
			case jml2b.structure.java.Type.T_DOUBLE :
				return new JavaTranslationResult("double",0);
			case jml2b.structure.java.Type.T_FLOAT :
				return new JavaTranslationResult("float",0);
			case jml2b.structure.java.Type.T_TYPE :
				return new JavaTranslationResult("\\TYPE",0);
			case jml2b.structure.java.Type.T_REF :
				return new JavaTranslationResult(getRefType().getName(),0);
			case jml2b.structure.java.Type.T_ARRAY :
				String res = new JavaType(getElemType()).toLang(indent).toUniqString();
				for (int i = 0; i < getDimension(); i++)
					res += "[]";
				return new JavaTranslationResult(res,0);
			default :
				throw new InternalError(
					"TTypeForm.toJava() unknown tag : " + getTag());
		}
	}

}
