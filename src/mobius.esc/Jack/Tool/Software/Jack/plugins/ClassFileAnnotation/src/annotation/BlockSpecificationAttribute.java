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

import jml2b.IJml2bConfiguration;
import jml2b.exceptions.Jml2bException;
import jml2b.exceptions.PogException;
import jml2b.structure.java.Method;
import jml2b.structure.jml.SpecCase;
import jml2b.structure.statement.StSpecBlock;

import org.apache.bcel.classfile.ConstantPool;

import util.ByteArray;

/**
 *
 *  @author L. Burdy
 **/
public class BlockSpecificationAttribute extends JmlAttributes {

	static final long serialVersionUID = 5030855968704751889L;

	private static byte[] getByteArray(
		IJml2bConfiguration config,
		JmlConstantPool jcp,
		Method m,
		org.apache.bcel.classfile.Method methodzz)
		throws PogException, Jml2bException {
		byte[] res = null;
		Vector asserts = new Vector();
		if (m.getBody(config) != null)
		m.getBody(config).getSpecBlock(asserts);
		Enumeration e = asserts.elements();
		while (e.hasMoreElements()) {
			StSpecBlock stb = (StSpecBlock) e.nextElement();
			short start =
				(short) AssertAttribute.getStartPC(stb.getStartLine() + 1, methodzz);
			short end =
				(short) AssertAttribute.getStartPC(
					stb.getEndLine(),
					methodzz);
			SpecCase ex = stb.getSp();
			if (res == null)
				res =
					ByteArray.addShort(
						start,
						ByteArray.addShort(
							end,
							JmlAttributes.getByteArray(
								config,
								jcp,
								ex,
								false,
								methodzz.getLocalVariableTable())));
			else
				res =
					ByteArray.concat(
						res,
						ByteArray.addShort(
							start,
							ByteArray.addShort(
								end,
								JmlAttributes.getByteArray(
									config,
									jcp,
									ex,
									false,
									methodzz.getLocalVariableTable()))));
		}
		return ByteArray.addShort((short) asserts.size(), res);
	}

	protected BlockSpecificationAttribute(
		IJml2bConfiguration config,
		JmlConstantPool jcp,
		ConstantPool cp,
		Method m,
		org.apache.bcel.classfile.Method methodzz)
		throws PogException, Jml2bException {
		super(
			IConstants.TAG_BLOCK_SPECIFICATION_ATTRIBUTE,
			jcp.createAttributeNameUtf8ConstantIndex("BlockSpecification"),
			getByteArray(config, jcp, m, methodzz),
			cp);
	}

}
