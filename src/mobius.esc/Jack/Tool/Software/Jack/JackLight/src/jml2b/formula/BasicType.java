//******************************************************************************
/* Copyright (c) 2004 INRIA. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: 
/*
/*******************************************************************************
/* Warnings/Remarks:
/******************************************************************************/

package jml2b.formula;

import java.io.IOException;

import jml2b.structure.AField;
import jml2b.util.IOutputStream;
import jml2b.util.JpoInputStream;

/**
 * Type of formula, the type can be
 * <UL>
 * <li> boolean
 * <li> integer
 * <li> reference
 * <li> proposition
 * <li> JML \TYPE
 * <li> function of two types.
 * </UL>
 * 
 * @author L. Burdy
 **/
public class BasicType {

	public final static int Z = 0;
	public final static int REF = 1;
	public final static int PROP = 2;
	public final static int BOOL = 3;
	public final static int TYPES = 4;
	public final static int FUNC = 5;

	public final static BasicType ZType = new BasicType(Z);
	public final static BasicType RefType = new BasicType(REF);
	public final static BasicType PropType = new BasicType(PROP);
	public final static BasicType BoolType = new BasicType(BOOL);
	public final static BasicType TypesType = new BasicType(TYPES);

	private int tag;
	private BasicType ltype, rtype;

	private BasicType(int tag) {
		this.tag = tag;
	}

	BasicType(AField f) {
		if (f.getType().isBoolean())
			tag = BOOL;
		else if (f.getType().isIntegral())
			tag = Z;
		else
			tag = REF;

		if (f.getModifiers() != null && !f.getModifiers().isStatic()) {
			ltype = RefType;
			rtype = new BasicType(tag);
			tag = FUNC;
		}
	}

	public BasicType(BasicType t1, BasicType t2) {
		tag = FUNC;
		ltype = t1;
		rtype = t2;
	}

	public BasicType(JpoInputStream s) throws IOException {
		tag = s.readByte();
		if (tag == FUNC) {
			ltype = new BasicType(s);
			rtype = new BasicType(s);
		}
	}

	/**
	 * @return
	 */
	public BasicType getRtype() {
		return rtype;
	}

	/**
	 * @return
	 */
	public BasicType getLtype() {
		return ltype;
	}

	public void save(IOutputStream s) throws IOException {
		s.writeByte(tag);
		if (tag == FUNC) {
			ltype.save(s);
			rtype.save(s);
		}
		
	}

	/**
	 * @return
	 */
	public int getTag() {
		return tag;
	}

}
