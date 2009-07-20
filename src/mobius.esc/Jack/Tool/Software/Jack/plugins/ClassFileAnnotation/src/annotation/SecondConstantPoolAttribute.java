//******************************************************************************
/* Copyright (c) 2004 INRIA. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: 
/*
/*******************************************************************************
/* Warnings/Remarks:
/******************************************************************************/
package annotation;

import java.io.ByteArrayOutputStream;
import java.io.DataOutputStream;
import java.io.IOException;
import java.io.OutputStream;
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
public class SecondConstantPoolAttribute extends JmlAttributes {

	/**
	 * 
	 */
	private static final long serialVersionUID = 1L;

	private static byte[] getByteArray(
		IJml2bConfiguration config,
		JmlConstantPool jcp,
		Class c)
		throws Jml2bException {
		ByteArrayOutputStream baos = new ByteArrayOutputStream();
		DataOutputStream dos = new DataOutputStream(baos);
		try {
			ConstantPool scp = jcp.getSecondConstantPool();
			  dos.writeShort(scp.getLength());
			    for(int i=0; i < scp.getLength(); i++)
			      if(scp.getConstant(i) != null)
				scp.getConstant(i).dump(dos);	
			baos.flush();
			dos.flush();
		} catch (IOException e1) {
			e1.printStackTrace();
		}
		return baos.toByteArray();
//		 byte[] att = baos.toByteArray();                                          
//		byte[] returnedba = new byte[att.length - 6];
//		for (int i=0; i < att.length -6;i++)
//			returnedba[i] = att[i+6];
//		return returnedba;		
	}

	public SecondConstantPoolAttribute(
		IJml2bConfiguration config,
		JmlConstantPool jcp,
		Class c,
		ConstantPool cp)
		throws Jml2bException {
		super(
			IConstants.TAG_SECOND_CONSTANT_POOL_ATTRIBUTE,
			jcp.createAttributeNameUtf8ConstantIndex("SecondConstantPool"),
			getByteArray(config, jcp, c),
			cp);
	}

}
