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
public class LoopSpecificationAttribute extends AttributeInfo {

	/** Name of the attribute as in the corresponding constant pool entry. */
	public static final String ATTRIBUTE_NAME = "LoopSpecification";

	Formula requires;
	LoopSpec[] spec;

	public LoopSpecificationAttribute(int attributeLength) {
		super(attributeLength);
	}

	public void read(DataInput in)
		throws InvalidByteCodeException, IOException {
		spec = new LoopSpec[in.readUnsignedShort()];
		for (int i = 0; i < spec.length; i++) {
			spec[i] = new LoopSpec(in);
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
	
	public String getLoopSpecText() {
		String res = "\n";
		for (int i=0; i < spec.length; i++) {
			if (i != 0)
				res += "   ;\n";
			res += spec[i].toString();	
		}
		return res += "\n";
	}

}

class LoopSpec {
	
	short index;
	Formula[] modifies;
	Formula invariant;
	Formula variant;
	
	LoopSpec (DataInput in) throws IOException {
		index = (short) in.readUnsignedShort();
		modifies = new Formula[in.readUnsignedShort()];
		for (int i=0; i < modifies.length; i++)
			modifies[i] = new Formula(in);
		invariant = new Formula(in);	
		variant = new Formula(in);	
	}
	
	
	public String toString() {
		String res ="@" + index + ":   modifies ";
		for (int i=0; i < modifies.length; i++) {
			if (i != 0)
				res += ",";
			res += modifies[i].toString();	 
		}
		res += "\n   invariant " + invariant + "\n   decreases " + variant + "\n";
		return res;
	}

}
