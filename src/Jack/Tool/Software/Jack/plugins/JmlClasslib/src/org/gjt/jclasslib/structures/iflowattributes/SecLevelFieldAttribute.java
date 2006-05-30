/*
 * Created on January 19, 2005
 *
 */
package org.gjt.jclasslib.structures.iflowattributes;

import java.io.DataInput;
import java.io.DataOutput;
import java.io.IOException;

import org.gjt.jclasslib.structures.AttributeInfo;
import org.gjt.jclasslib.structures.InvalidByteCodeException;

/**
 *
 *  @author L. Burdy, Luca Martini
 **/
public class SecLevelFieldAttribute extends AttributeInfo {

    public byte level;

    /** Name of the attribute as in the corresponding constant pool entry. */
    public static final String ATTRIBUTE_NAME = "SecLevelField";
    
    
    public SecLevelFieldAttribute(int attributeLength) {
	super(attributeLength);
    }
    
    public void read(DataInput in)
	throws InvalidByteCodeException, IOException {
	level = in.readByte();
    }

    public void write(DataOutput out)
	throws InvalidByteCodeException, IOException {
    }

}

