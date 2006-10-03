//******************************************************************************
/* Copyright (c) 2004 INRIA. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: 
/*
/*******************************************************************************
/* Warnings/Remarks:
/******************************************************************************/
package annotation;

import java.io.DataOutputStream;
import java.io.IOException;
import java.util.Enumeration;
import java.util.Vector;

import jml2b.IJml2bConfiguration;

import org.apache.bcel.classfile.ConstantPool;

/**
 *
 *  @author L. Burdy
 **/
public class ModelMethodAttribute extends JmlAttributes {


	/**
	 * 
	 */
	private static final long serialVersionUID = 1L;
	IJml2bConfiguration config;
	
	private static byte getByteArrayLength(Vector ann, JmlConstantPool jcp) {
		byte size = 2;
		Enumeration e = ann.elements();
		while (e.hasMoreElements()) {
			JmlMethod jm = (JmlMethod) e.nextElement();
			size += 8 + jm.getAttributesSize();
		}
		return size;

	}
	
	Vector methods;

	protected ModelMethodAttribute(IJml2bConfiguration config,
		ConstantPool cp,
		JmlConstantPool jcp,
		Vector methods) {
		super(
			IConstants.TAG_MODEL_METHOD_ATTRIBUTE,
			jcp.createAttributeNameUtf8ConstantIndex("Model_Method"),
			getByteArrayLength(methods, jcp),
			cp);
		this.config = config;
		this.methods = methods;
	}

	public void dump(DataOutputStream file) throws IOException {
		dumpEntete(file);
		file.writeShort(methods.size());
		Enumeration e = methods.elements();
		while (e.hasMoreElements()) {
			JmlMethod jm = (JmlMethod) e.nextElement();
			jm.dump(config, file);
		}
	}


}
