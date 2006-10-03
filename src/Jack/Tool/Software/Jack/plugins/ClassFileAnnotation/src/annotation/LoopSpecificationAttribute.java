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
import jml2b.exceptions.PogException;
import jml2b.structure.java.Method;
import jml2b.structure.statement.StLoops;
import jml2b.structure.statement.TerminalExp;

import org.apache.bcel.classfile.ConstantPool;

import util.ByteArray;

/**
 * 
 * @author L. Burdy
 */
public class LoopSpecificationAttribute extends JmlAttributes {

	/**
	 * 
	 */
	private static final long serialVersionUID = 1L;
	private static byte[] getByteArray(IJml2bConfiguration config, JmlConstantPool jcp, Method m,
			org.apache.bcel.classfile.Method methodzz) throws PogException, Jml2bException {
		byte[] res = null;
		Vector loops = new Vector();
		if (m.getBody(config) != null)
			m.getBody(config).getLoop(loops);
		Enumeration e = loops.elements();
		while (e.hasMoreElements()) {
			StLoops sta = (StLoops) e.nextElement();
			int line = 0;
			if (sta.getNodeType() == JmlDeclParserTokenTypes.LITERAL_do)
				line = sta.getBody().firstStatement().getLine() + 1;
			else
				line = sta.getLine() + 1;
			short pc = (short) AssertAttribute.getStartPC(line, methodzz);
			if (res == null)
				res = ByteArray.addShort(pc, JmlAttributes.getByteArray(config, jcp, sta.getLoop_modifies(), methodzz
						.getLocalVariableTable()));
			else
				res = ByteArray.concat(res, ByteArray.addShort(pc, JmlAttributes.getByteArray(config, jcp, sta
						.getLoop_modifies(), methodzz.getLocalVariableTable())));
			res = ByteArray.concat(res, JmlAttributes.getByteArray(	config,
																	jcp,
																	sta.getLoop_invariant(),
																	false,
																	new Vector(),
																	methodzz.getLocalVariableTable()));
			if (sta.getLoop_variant() == null)
				res = ByteArray.concat(res, JmlAttributes.getByteArray(config, jcp, new TerminalExp(
						JmlDeclParserTokenTypes.NUM_INT, "1"), false, new Vector(), methodzz.getLocalVariableTable()));
			else
				res = ByteArray.concat(res, JmlAttributes.getByteArray(	config,
																		jcp,
																		sta.getLoop_variant(),
																		false,
																		new Vector(),
																		methodzz.getLocalVariableTable()));
			//			byte[] specEx = null;
			//			Enumeration e1 = sta.getLoop_exsures().elements();
			//			byte exsuresCount = 0;
			//			while (e1.hasMoreElements()) {
			//				Exsures ex = (Exsures) e1.nextElement();
			//				exsuresCount++;
			//				if (specEx == null)
			//					specEx =
			//						JmlAttributes.getByteArray(
			//							config,
			//							jcp,
			//							ex,
			//							m.signature.signature);
			//				else
			//					specEx =
			//						ByteArray.concat(
			//							specEx,
			//							JmlAttributes.getByteArray(
			//								config,
			//								jcp,
			//								ex,
			//								m.signature.signature));
			//			}
			//			specEx = ByteArray.addShort((short) exsuresCount, specEx);
			//			res = ByteArray.concat(res, specEx);
		}
		//		if (res == null)
		//			return new byte[0];
		res = ByteArray.addShort((short) loops.size(), res);
		return res;
	}
	protected LoopSpecificationAttribute(IJml2bConfiguration config, JmlConstantPool jcp, ConstantPool cp, Method m,
			org.apache.bcel.classfile.Method methodzz) throws PogException, Jml2bException {
		super(IConstants.TAG_LOOP_SPECIFICATION_ATTRIBUTE, jcp.createAttributeNameUtf8ConstantIndex("LoopSpecification"),
				getByteArray(config, jcp, m, methodzz), cp);
	}

}