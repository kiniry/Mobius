/*
 * Created on January 19, 2005
 *
 */
package org.gjt.jclasslib.structures.iflowattributes;


import java.io.DataInput;
import java.io.DataOutput;
import java.io.IOException;
import java.util.BitSet;
import org.gjt.jclasslib.structures.AttributeInfo;
import org.gjt.jclasslib.structures.InvalidByteCodeException;

/**
 *
 *  @author L. Burdy, Luca Martini
 **/
public class SecLevelMethodAttribute extends AttributeInfo {
    byte effect;
    byte exceffect;
    byte impl_par;
    byte return_value;
    byte[] register;
    short registers_count;
    BitSet arrays;

    /** Name of the attribute as in the corresponding constant pool entry. */
    public static final String ATTRIBUTE_NAME = "SecLevelMethod";
    
    
    public SecLevelMethodAttribute(int attributeLength) {
	super(attributeLength);
    }
    
    public void read(DataInput in)
	throws InvalidByteCodeException, IOException {
	registers_count = in.readShort();
	arrays = new BitSet(registers_count);
	register = new byte[registers_count];
	// read the registers information
	for (int i = 0; i < registers_count; i++) {
	    register[i] = in.readByte();
	    switch (in.readByte()) {
	    case (byte)0xff:
		arrays.set(i);
		break;

	    case (byte)0x00:
		break;

	    default:
		throw new InvalidByteCodeException();
	    }
	    
	}
	effect=in.readByte();
	exceffect=in.readByte();
	impl_par=in.readByte();
	return_value=in.readByte();
    }

    public void write(DataOutput out)
	throws InvalidByteCodeException, IOException {
    }

    public byte[] getRegisters() {
	return register;
    }
    
    public byte getReturn_value() {
	return return_value;
    }
    

    public byte getExceffect() {
	return exceffect;
    }

    public byte getEffect() {
	return effect;
    }
    
    public byte getImpl_Par() {
	return impl_par;
    }

    public boolean isArray(int i) {
	return arrays.get(i);
    }
}

