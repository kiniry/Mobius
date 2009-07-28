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
public class AssertAttribute extends AttributeInfo {

	/** Name of the attribute as in the corresponding constant pool entry. */
	public static final String ATTRIBUTE_NAME = "Assert";

	Assert[] assert;

	public AssertAttribute(int attributeLength) {
		super(attributeLength);
	}

	public void read(DataInput in)
		throws InvalidByteCodeException, IOException {
		assert = new Assert[in.readUnsignedShort()];
		for (int i = 0; i < assert.length; i++) {
			assert[i] = new Assert(in);
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

	public String getAssertText() {
		String res = "\n";
		for (int i = 0; i < assert.length; i++) {
			if (i != 0)
				res += "   ;\n";
			res += assert[i].toString();
		}
		return res += "\n";
	}

}

class Assert {

	short index;
	Formula assert;

	Assert(DataInput in) throws IOException {
		index = (short) in.readUnsignedShort();
		assert = new Formula(in);
	}

	public String toString() {
		return "@" + index + " " + assert;
	}

}
