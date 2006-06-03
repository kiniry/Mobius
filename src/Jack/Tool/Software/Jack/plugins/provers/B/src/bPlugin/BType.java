//******************************************************************************
/* Copyright (c) 2003, 2004 INRIA. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: 
/*
/*******************************************************************************
/* Warnings/Remarks:
/******************************************************************************/

package bPlugin;

import jack.util.Logger;
import jml2b.exceptions.LanguageException;
import jml2b.languages.ITranslatable;
import jml2b.languages.ITranslationResult;
import jml2b.structure.java.Type;

/**
 * @author lburdy
 *
 * To change the template for this generated type comment go to
 * Window&gt;Preferences&gt;Java&gt;Code Generation&gt;Code and Comments
 */
public class BType extends Type implements ITranslatable {

	static final long serialVersionUID = -6632178672370536943L;

	BType(Type t) {
		tag = t.getTag();
		refType = t.getRefType();
		elemType = t.getElemType();
	}	

	/**
	 * Converts the type to a B representation.
	 * 
	 * @return String a string representing the type in a B-like 
	 *     notation.
	 */
	public ITranslationResult toLang(int indent) throws LanguageException {
		switch (tag) {
			case Type.T_BOOLEAN :
				return new BTranslationResult("BOOL");
			case Type.T_INT :
				return new BTranslationResult("t_int");
			case Type.T_SHORT :
				return new BTranslationResult("t_short");
			case Type.T_BYTE :
				return new BTranslationResult("t_byte");
			case Type.T_CHAR :
				return new BTranslationResult("t_char");
			case Type.T_LONG :
				return new BTranslationResult("t_long");
			case Type.T_DOUBLE :
				return new BTranslationResult("t_double");
			case Type.T_FLOAT :
				return new BTranslationResult("t_float");
			case Type.T_REF :
			case Type.T_ARRAY :
			default :
				return new BTranslationResult(getBType(0));
		}
	}

	/**
	 * return the B type of the given type. This type must be ref of refarray
	 */
	protected String getBType(int dimension) throws LanguageException {
		switch (tag) {
			case Type.T_INT :
				return getBType(BPrinter.c_int, dimension);
			case Type.T_SHORT :
				return getBType(BPrinter.c_short, dimension);
			case Type.T_BYTE :
				return getBType(BPrinter.c_byte, dimension);
			case Type.T_BOOLEAN :
				return getBType(BPrinter.c_boolean, dimension);
			case Type.T_CHAR :
				return getBType(BPrinter.c_char, dimension);
				//	case T_VOID:
				//	    return "void";
			case Type.T_LONG :
				return getBType("c_long", dimension);
			case Type.T_DOUBLE :
				return getBType("c_double", dimension);
			case Type.T_FLOAT :
				return getBType("c_float", dimension);
			case T_TYPE :
				return BPrinter.TYPES;
			case Type.T_REF :
				BClass clzz = BPrinter.getBClass(refType);
				if(clzz == null) {
					// ...and we print the warning
					Logger.err.println("Type unknown");
					return BPrinter.TYPES;
				}
				return getBType(clzz.enumerationRank + "|->" + BPrinter.NAMES, dimension);
			case Type.T_ARRAY :
				return new BType(elemType).getBType(dimension + 1);
			default :
				// return "<unknown>";
				throw new InternalError(
					"getBType called with incorrect type: "
						+ tag
						+ " (dimension = "
						+ dimension
						+ ")");
		}
	}

	protected String getBType(String str, int dimension) {
		return "(" + str + " |-> " + dimension + ")";
	}

}
