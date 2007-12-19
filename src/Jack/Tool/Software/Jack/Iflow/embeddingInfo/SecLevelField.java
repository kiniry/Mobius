package embeddingInfo;
/*
 * Created on Jan 13, 2005
 * @version $Id: SecLevelField.java,v 1.3 2005/03/21 09:36:38 lmartini Exp $
 */

/**
 * @author Luca Martini
 *
 */

import org.apache.bcel.classfile.Attribute;
import org.apache.bcel.classfile.ConstantPool;
import org.apache.bcel.classfile.Visitor;
import java.io.DataOutputStream;
import java.io.IOException;

public class SecLevelField extends AbstractSecLevelField {
    public SecLevelField( short name_index, 
			 ConstantPool cp, 
			 byte level) {
	super(name_index,cp,level);
	sl = new HL(level,false);
    }

    public Attribute copy(ConstantPool constant_pool) {
	return this;
    }
    
    public void accept(Visitor v) {
	return;
    }
    
    public String toString() {
	return ("[SecLevelField] "+ sl);
    }
}

