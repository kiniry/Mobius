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
import jml2b.structure.AField;
import jml2b.structure.java.Modifiers;

import org.apache.bcel.classfile.ConstantPool;

/**
 *
 *  @author L. Burdy
 **/
public class ModelFieldAttribute extends JmlAttributes {

	/**
	 * 
	 */
	private static final long serialVersionUID = 1L;

	private static byte[] getByteArray(IJml2bConfiguration config, Vector ann, JmlConstantPool jcp) {
		byte fields_count = (byte) ann.size();
		byte[] tmp = new byte[2 + 6 * fields_count];
		Enumeration e = ann.elements();
		int l = 0;
		tmp[l++] = (byte) (fields_count / 256);
		tmp[l++] = (byte) (fields_count % 256);
		while (e.hasMoreElements()) {
			AField a = (AField) e.nextElement();
			byte acces_flag = getAccesFlag(a.getModifiers());
			short name_index = jcp.getOrCreateNameIndex(a);
			short descriptor_index = jcp.getOrCreateDescriptorIndex(config, a.getType());
			tmp[l++] = (byte) (acces_flag / 256);
			tmp[l++] = (byte) (acces_flag % 256);
			tmp[l++] = (byte) (name_index / 256);
			tmp[l++] = (byte) (name_index % 256);
			tmp[l++] = (byte) (descriptor_index / 256);
			tmp[l++] = (byte) (descriptor_index % 256);
		}
		return tmp;
	}

	protected ModelFieldAttribute(
			IJml2bConfiguration config, 
		ConstantPool cp,
		JmlConstantPool jcp,
		Vector fields) {
		super(
			IConstants.TAG_MODEL_FIELD_ATTRIBUTE,
			jcp.createAttributeNameUtf8ConstantIndex("ModelField"),
			getByteArray(config, fields, jcp),
			cp);
	}

}
