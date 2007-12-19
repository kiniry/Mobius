package embeddingInfo;
/*
 * Created on Jan 18, 2005
 * @version $Id: SecLevelMethod.java,v 1.3 2005/02/17 12:46:10 lmartini Exp $
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

public class SecLevelMethod extends AbstractSecLevelMethod {
    public SecLevelMethod( short name_index, 
			   ConstantPool cp, 
			   short registers_count) {
	super(name_index, cp, registers_count);
	effect = new HL();
	exceffect = new HL();
	impl_par = new HL();
	return_value = new HL();
	for (int i = 0; i < registers_count; i++) 
	     registers[i] = new HL();
    }
    
    public Attribute copy(ConstantPool constant_pool) {
	return this;
    }
    
    public void accept(Visitor v) {
	return;
    }
    
    public String toString() {
	return ("[SecLevelMethod] "+impl_par);
    }

//     public final void dump(DataOutputStream file) throws IOException {
// 	super.dump(file);
// 	file.writeShort(registers_count);
// 	file.write(registers);
// 	file.writeByte(effect);
// 	file.writeByte(exceffect);
// 	file.writeByte(impl_par);
// 	file.writeByte(return_value);
//     }
}
