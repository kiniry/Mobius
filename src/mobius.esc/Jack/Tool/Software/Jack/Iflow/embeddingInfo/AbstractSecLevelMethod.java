package embeddingInfo;
/*
 * Created on Jan 18, 2005
 * @version $Id: AbstractSecLevelMethod.java,v 1.2 2005/03/21 09:36:37 lmartini Exp $
 */

/**
 * @author Luca Martini
 *
 */

import java.io.DataOutputStream;
import java.io.IOException;
import java.util.BitSet;
import org.apache.bcel.classfile.Attribute;
import org.apache.bcel.classfile.ConstantPool;

public abstract class AbstractSecLevelMethod extends Attribute {
    
    /**
     * <code>TRUE</code> represents a true boolean value converted in
     * byte.
     */
    public static final byte TRUE = (byte) 0xff;
    
    /**
     * <code>FALSE</code> represents a false boolean value converted in
     * byte.
     */
    public static final byte FALSE = (byte) 0x00;
    
    /**
     * The method effect on the heap.
     *
     */
    public SecLevel effect;

    /**
     * The method effect on exceptions
     *
     */
    public SecLevel exceffect;
    
    /**
     * This is the security level of the implicit parameter (equal to
     * the s.l. of the register zero)
     *
     */
    public SecLevel impl_par;
    
    /**
     * The security level of the return valued of the
     * method. (Unmeaningful for void methods)
     *
     */
    public SecLevel return_value;
    
    /**
     * The security levels of the local variables used by the method.
     *
     */
    public SecLevel[] registers;
    
    /**
     * The number of register used by the method.
     *
     */
    public short registers_count;

    /**
     * This <code>BitSet</code> records which of the registers
     * contains array values.
     */
    protected BitSet b;

    public AbstractSecLevelMethod( short name_index, 
			   ConstantPool cp, 
			   short registers_count) {
	super(Constants.TAG_SECLEVELMETHD, name_index, 6+2*registers_count, cp);
	this.registers_count = registers_count;
	registers = new SecLevel[registers_count];
	b = new BitSet(registers_count);
    }
    
    public final void dump(DataOutputStream file) throws IOException {
	super.dump(file);
	file.writeShort(registers_count);
	for (int i = 0; i < registers_count; i++) {
	    file.writeByte(registers[i].level);
	    file.writeByte((b.get(i))?TRUE:FALSE);
	}
	file.writeByte(effect.level);
	file.writeByte(exceffect.level);
	file.writeByte(impl_par.level);
	file.writeByte(return_value.level);

    }

    public final boolean isArray(int i) {
	return b.get(i);
    }
    
    public String toString() {
	return (registers_count +" registers");
    }
}
