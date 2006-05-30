/*
 * Created on May 26, 2004
 *
 * To change the template for this generated file go to
 * Window&gt;Preferences&gt;Java&gt;Code Generation&gt;Code and Comments
 */
package org.gjt.jclasslib.structures.jmlattributes;

import java.io.DataInput;
import java.io.DataOutput;
import java.io.IOException;

import org.gjt.jclasslib.structures.AttributeInfo;
import org.gjt.jclasslib.structures.InvalidByteCodeException;

/**
 *
 *  @author L. Burdy
 **/
public class MethodSpecificationAttribute extends AttributeInfo {

	/** Name of the attribute as in the corresponding constant pool entry. */
	public static final String ATTRIBUTE_NAME = "MethodSpecification";

	Formula requires;
	MethodSpec[] spec;

	public MethodSpecificationAttribute(int attributeLength) {
		super(attributeLength);
	}

	public void read(DataInput in)
		throws InvalidByteCodeException, IOException {
		requires = new Formula(in);
		int specCount = in.readUnsignedShort();
		spec = new MethodSpec[specCount];
		for (int i = 0; i < specCount; i++) {
			spec[i] = new MethodSpec(in);
		}
	}

	public void write(DataOutput out)
		throws InvalidByteCodeException, IOException {
	}

	/**
	 * @return
	 */
	public int getSourcefileIndex() {
		// TODO Auto-generated method stub
		return 0;
	}

	/**
	 * @return
	 */
	public Formula getRequires() {
		return requires;
	}
	
//	public String getSpecText() {
//		String res = "\n{|\n";
//		for (int i=0; i < spec.length; i++) {
//			if (i != 0)
//				res += "   also\n";
//			res += spec[i].toString();	
//		}
//		return res += "\n|}";
//	}

	/**
	 * @return
	 */
	public MethodSpec[] getSpec() {
		return spec;
	}

}

