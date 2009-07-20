package embeddingInfo; 
/*
 * Created on Jan 24, 2005
 * @version $Id: SLMethodAttributeReader.java,v 1.2 2005/03/21 09:36:38 lmartini Exp $
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



public class SLMethodAttributeReader implements AttributeReader {
    
    public Attribute createAttribute(int index_name, int length, DataInputStream is, ConstantPool cp)  {
	short reg_count;
	SecLevelMethod slm;
	try {	    
	    reg_count = is.readShort();
	    slm = new SecLevelMethod((short) index_name, cp, (short) reg_count);
	    for (int i = 0; i < slm.registers_count; i++) {
		SecLevel temp = slm.registers[i]; // temporary reference to speedup method
		temp.level = is.readByte();
		switch (is.readByte()) {
		case AbstractSecLevelMethod.TRUE:
		    slm.b.set(i);
		    temp.isArray = true;
		    temp.levelArray=temp.level; 
		    break;
		case AbstractSecLevelMethod.FALSE:
		    break;
		default:
		    System.out.println("Parsing error in the classfile. Aborting...");
		    System.exit(0);
		    break;
		}
	    }
	    slm.effect.level = is.readByte();
	    slm.exceffect.level = is.readByte();
	    slm.impl_par.level = is.readByte();
	    slm.return_value.level = is.readByte();
	} catch (IOException e) {
	    return null;
	}
	return slm;
    }
}    
