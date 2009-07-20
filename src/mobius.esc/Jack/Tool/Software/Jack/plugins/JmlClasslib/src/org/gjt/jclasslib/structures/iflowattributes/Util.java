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
 *  @author Luca Martini
 **/
public class Util {
    public static String secLeveByte2String(byte b) {
	if (b == 0x00)
	    return "L";
	if (b == 0x01)
	    return "H";
	return "X";
    }
}