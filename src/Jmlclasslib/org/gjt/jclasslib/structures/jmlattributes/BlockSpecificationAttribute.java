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
public class BlockSpecificationAttribute extends AttributeInfo {

	/** Name of the attribute as in the corresponding constant pool entry. */
	public static final String ATTRIBUTE_NAME = "BlockSpecification";

	BlockSpec[] spec;

	public BlockSpecificationAttribute(int attributeLength) {
		super(attributeLength);
	}

	public void read(DataInput in)
		throws InvalidByteCodeException, IOException {
		spec = new BlockSpec[in.readUnsignedShort()];
		for (int i = 0; i < spec.length; i++) {
			spec[i] = new BlockSpec(in);
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

	public String getBlockSpecText() {
		String res = "\n";
		for (int i=0; i < spec.length; i++) {
			if (i != 0)
				res += "   ;\n";
			res += spec[i].toString();	
		}
		return res += "\n";
	}

	/**
	 * @return
	 */
	public BlockSpec[] getSpec() {
		return spec;
	}

}

