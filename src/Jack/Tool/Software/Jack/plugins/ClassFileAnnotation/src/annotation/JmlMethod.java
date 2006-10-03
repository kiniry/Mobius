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

import jml2b.IJml2bConfiguration;
import jml2b.structure.java.Method;
import jml2b.structure.java.Modifiers;
import jml2b.structure.java.Parameters;

import org.apache.bcel.classfile.Attribute;

/**
 *
 *  @author L. Burdy
 **/
public class JmlMethod {

	Method m;

	Attribute[] aa;

	JmlConstantPool jcp;

	JmlMethod(Method m, Attribute[] aa, JmlConstantPool jcp) {
		this.m = m;
		this.aa = aa;
		this.jcp = jcp;
	}

	public int getAttributesSize() {
		int res = 0;
		for (int i = 0; i < aa.length; i++) {
			res += aa[i].getLength();
		}
		return res;
	}

	public void dump(IJml2bConfiguration config, DataOutputStream file) throws IOException {
		byte[] tmp = new byte[8];
		int l = 0;
		byte acces_flag = JmlAttributes.getAccesFlag((Modifiers) m.getModifiers());
		short name_index = jcp.getOrCreateNameIndex(m);
		short descriptor_index =
			jcp.getOrCreateDescriptorIndex(config, (Parameters) m.getParams(), m.getReturnType());
		byte attributes_count = (byte) aa.length;
		tmp[l++] = (byte) (acces_flag / 256);
		tmp[l++] = (byte) (acces_flag % 256);
		tmp[l++] = (byte) (name_index / 256);
		tmp[l++] = (byte) (name_index % 256);
		tmp[l++] = (byte) (descriptor_index / 256);
		tmp[l++] = (byte) (descriptor_index % 256);
		tmp[l++] = (byte) (attributes_count / 256);
		tmp[l++] = (byte) (attributes_count % 256);
		for (int i = 0; i < aa.length; i++)
			aa[i].dump(file);
	}

}

