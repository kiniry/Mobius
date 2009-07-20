package embeddingInfo; 
/*
 * Created on Jan 21, 2005
 * @version $Id: SLFieldAttributeReader.java,v 1.1 2005/02/02 14:40:10 lmartini Exp $
 */

/**
 * @author Luca Martini
 *
 */


import java.io.DataInputStream;
import java.io.IOException;
import org.apache.bcel.classfile.Attribute;
import org.apache.bcel.classfile.AttributeReader;
import org.apache.bcel.classfile.ConstantPool;
import org.apache.bcel.classfile.Visitor;


public class SLFieldAttributeReader implements AttributeReader {
    
    public Attribute createAttribute(int index_name, int length, DataInputStream is, ConstantPool cp)  {
	byte level;
	try {	    
	    level = is.readByte();	
	} catch (IOException e) {
	    return null;
	}
	return new SecLevelField((short)index_name, cp, level); 
    }
}    
