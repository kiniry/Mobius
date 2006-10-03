//******************************************************************************
/* Copyright (c) 2004 INRIA. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: 
/*
/*******************************************************************************
/* Warnings/Remarks:
/******************************************************************************/
package annotation;

import java.util.Enumeration;
import java.util.Vector;

import jml.JmlDeclParserTokenTypes;
import jml2b.IJml2bConfiguration;
import jml2b.exceptions.Jml2bException;
import jml2b.structure.java.Class;
import jml2b.structure.java.Invariant;
import jml2b.structure.statement.BinaryExp;
import jml2b.structure.statement.Expression;

import org.apache.bcel.classfile.ConstantPool;

/**
 *
 *  @author L. Burdy
 **/
public class ConstraintAttribute extends JmlAttributes {

	/**
	 * 
	 */
	private static final long serialVersionUID = 1L;

	private static byte[] getByteArray(
		IJml2bConfiguration config,
		JmlConstantPool jcp,
		Class c)
		throws Jml2bException {
		Expression exp = null;
		Enumeration e = c.getConstraints();
		while (e.hasMoreElements()) {
			Invariant i = (Invariant) e.nextElement();
			if (exp == null)
				exp = i.getInvariant();
			else
				exp =
					new BinaryExp(
						JmlDeclParserTokenTypes.LOGICAL_OP,
						exp,
						"&&",
						i.getInvariant());
		}
		if (exp == null)
			return new byte[] { 0x00 };
		return getByteArray(config, jcp, exp, false, new Vector(), null);
	}

	public ConstraintAttribute(
		IJml2bConfiguration config,
		JmlConstantPool jcp,
		Class c,
		ConstantPool cp)
		throws Jml2bException {
		super(
			IConstants.TAG_CONSTRAINT_ATTRIBUTE,
			jcp.createAttributeNameUtf8ConstantIndex("Constraint"),
			getByteArray(config, jcp, c),
			cp);
	}

}
