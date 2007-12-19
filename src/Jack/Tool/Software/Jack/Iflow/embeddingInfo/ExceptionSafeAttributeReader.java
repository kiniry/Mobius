package embeddingInfo; 
/*
 * Created on Mar 17, 2005
 * @version $Id: ExceptionSafeAttributeReader.java,v 1.1 2005/03/21 09:36:37 lmartini Exp $
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


public class ExceptionSafeAttributeReader implements AttributeReader {
    
    public Attribute createAttribute(int index_name, int length, DataInputStream is, ConstantPool cp)  {
	ExceptionSafe es;
	short excIndex;
	try {
	    excIndex = is.readShort();
	    es = new ExceptionSafe((short) index_name, cp,excIndex);
	    short numpcs = is.readShort();
	    for (int i = 0; i < numpcs; i++) {
		// does not check the return value of addPc
		es.addPc(is.readShort());
	    }
	    
	} catch (IOException e) {
	    return null ;
	}
	return es;
    }
}    
