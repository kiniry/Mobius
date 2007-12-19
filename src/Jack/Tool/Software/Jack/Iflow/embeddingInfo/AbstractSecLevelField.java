package embeddingInfo;
/*
 * Created on Jan 21, 2005
 * @version $Id: AbstractSecLevelField.java,v 1.2 2005/03/21 09:36:37 lmartini Exp $
 */

/**
 * @author Luca Martini
 *
 */

import org.apache.bcel.classfile.Attribute;
import org.apache.bcel.classfile.ConstantPool;
import java.io.DataOutputStream;
import java.io.IOException;

public abstract class AbstractSecLevelField extends Attribute {
    public SecLevel sl;
    public AbstractSecLevelField( short name_index, 
			 ConstantPool cp, 
			 byte level) {
	super(Constants.TAG_SECLEVELFIELD, name_index, 1, cp);
    }
    
    public final void dump(DataOutputStream file) throws IOException {
	super.dump(file);
	file.writeByte(sl.level);
    }
}

    

