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

import org.apache.bcel.classfile.ConstantPool;
import org.apache.bcel.classfile.LocalVariableTable;

import util.ByteArray;

/**
 *
 *  @author L. Burdy
 **/
public class MethodSpecificationAttribute extends JmlAttributes {

	/**
	 * 
	 */
	private static final long serialVersionUID = 1L;

	private static byte[] getByteArray(
		IJml2bConfiguration config,
		JmlConstantPool jcp,
		Method m,
		org.apache.bcel.classfile.Method methodzz)
		throws Jml2bException, PogException {
		Vector specC = m.getSpecCasesV(config);
		byte specCount = (byte) specC.size();
		byte[] specBA = null;
		Enumeration e = specC.elements();
		while (e.hasMoreElements()) {
			SpecCase element = (SpecCase) e.nextElement();
			LocalVariableTable lvt = null;
			if ( methodzz != null) {
				lvt =  methodzz.getLocalVariableTable();
			} 
			if (specBA == null)
				specBA =
					JmlAttributes.getByteArray(
						config,
						jcp,
						element,
						true,
						lvt);
			else
				specBA =
					ByteArray.concat(
						specBA,
						JmlAttributes.getByteArray(
							config,
							jcp,
							element,
							true,
							lvt));
		}
		if (specBA == null)
			return new byte[0];
		specBA = ByteArray.addShort(specCount, specBA);
		return ByteArray.concat(
			JmlAttributes.getByteArray(
				config,
				jcp,
				m.getNormalizedRequires(config),
				false,
				new Vector(),
				methodzz.getLocalVariableTable()),
			specBA);
	}

	protected MethodSpecificationAttribute(
		IJml2bConfiguration config,
		JmlConstantPool jcp,
		ConstantPool cp,
		Method m,
		org.apache.bcel.classfile.Method methodzz)
		throws Jml2bException, PogException {
		super(
			IConstants.TAG_METHOD_SPECIFICATION_ATTRIBUTE,
			jcp.createAttributeNameUtf8ConstantIndex("MethodSpecification"),
			getByteArray(config, jcp, m, methodzz),
			cp);
	}

}
