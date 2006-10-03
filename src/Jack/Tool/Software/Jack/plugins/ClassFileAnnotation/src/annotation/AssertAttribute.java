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
import jml2b.structure.statement.Expression;
import jml2b.structure.statement.StAssert;

import org.apache.bcel.classfile.ConstantPool;
import org.apache.bcel.classfile.LineNumber;

import util.ByteArray;

/**
 * 
 * @author L. Burdy
 */
public class AssertAttribute extends JmlAttributes {

	static final long serialVersionUID = 6560131004056072310L;

	static int getStartPC(int line, org.apache.bcel.classfile.Method methodzz) {
		LineNumber[] lna = methodzz.getLineNumberTable().getLineNumberTable();
		int res = -1;
		for (int i = 0; i < lna.length; i++) {
			if (lna[i].getLineNumber() >= line) {
				if (i == 0)
					return 0;
				else {
					res = lna[i].getStartPC();//i;
					for (int j = i + 1; j < lna.length; j++)
						if (lna[j].getLineNumber() == line)
							res = lna[j].getStartPC();//j;
					return res;
				}
			}
		}
		return res;
	}

	private static byte[] getByteArray(IJml2bConfiguration config, JmlConstantPool jcp, Method m,
			org.apache.bcel.classfile.Method methodzz) throws PogException, Jml2bException {
		byte[] res = null;
		Vector asserts = new Vector();
		if (m.getBody(config) != null)
		m.getBody(config).getAssert(asserts);
		Enumeration e = asserts.elements();
		while (e.hasMoreElements()) {
			StAssert sta = (StAssert) e.nextElement();
			short pc = (short) getStartPC(sta.getLine() + 1, methodzz);
			Expression ex = sta.getExp();
			if (res == null)
				res = ByteArray.addShort(pc, JmlAttributes.getByteArray(config, jcp, ex, false, new Vector(), methodzz
						.getLocalVariableTable()));
			else
				res = ByteArray.concat(res, ByteArray.addShort(pc, JmlAttributes
						.getByteArray(config, jcp, ex, false, new Vector(), methodzz.getLocalVariableTable())));
		}
		return ByteArray.addShort((short) asserts.size(), res);
	}

	protected AssertAttribute(IJml2bConfiguration config, JmlConstantPool jcp, ConstantPool cp, Method m,
			org.apache.bcel.classfile.Method methodzz) throws Jml2bException, PogException {
		super(IConstants.TAG_ASSERT_ATTRIBUTE, jcp.createAttributeNameUtf8ConstantIndex("Assert"), getByteArray(config,
																										jcp,
																										m,
																										methodzz), cp);
	}

}