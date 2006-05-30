//******************************************************************************
/* Copyright (c) 2004 INRIA. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: 
/*
/*******************************************************************************
/* Warnings/Remarks:
/******************************************************************************/

package bPlugin;

import jml2b.IJml2bConfiguration;
import jml2b.structure.java.Type;

/**
 * @author lburdy
 *
 * To change the template for this generated type comment go to
 * Window&gt;Preferences&gt;Java&gt;Code Generation&gt;Code and Comments
 */
public class BDisplayedType extends BType {

	static final long serialVersionUID = -6523407669497195886L;

	BDisplayedType(Type t) {
		super(t);
	}

	/**
	 * return the B type of the given type. This type must be ref of refarray
	 */
	protected String getBType(IJml2bConfiguration config, int dimension) {
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
				return refType.getBName();
			case Type.T_ARRAY :
				return new BDisplayedType(elemType).getBType(config, dimension + 1);
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

}
