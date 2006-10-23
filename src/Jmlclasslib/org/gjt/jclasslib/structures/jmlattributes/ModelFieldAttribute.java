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
public class ModelFieldAttribute extends AttributeInfo {

	/** Name of the attribute as in the corresponding constant pool entry. */
	public static final String ATTRIBUTE_NAME = "ModelField";

	Field[] fields;

	public ModelFieldAttribute(int attributeLength) {
		super(attributeLength);
	}

	public void read(DataInput in)
		throws InvalidByteCodeException, IOException {
		fields = new Field[in.readUnsignedShort()];
		for (int i = 0; i < fields.length; i++) {
			fields[i] = new Field(in);
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
		for (int i = 0; i < fields.length; i++) {
			if (i != 0)
				res += "   ;\n";
			res += fields[i].toString();
		}
		return res += "\n";
	}

}

class Field {

	short accesFlag;
	short nameIndex;
	short descriptorIndex;

	Field(DataInput in) throws IOException {
		accesFlag = (short) in.readUnsignedShort();
		nameIndex = (short) in.readUnsignedShort();
		descriptorIndex = (short) in.readUnsignedShort();
	}

	public String toString() {
		return "acces flag: "
			+ accesFlag
			+ "; name index: "
			+ nameIndex
			+ "; desc index: "
			+ descriptorIndex + "\n";
	}

}
