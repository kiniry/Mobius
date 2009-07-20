package embeddingInfo;
/*
 * Created on March 17, 2005
 * @version $Id: ExceptionSafe.java,v 1.1 2005/03/21 09:36:37 lmartini Exp $
 */

/**
 * @author Luca Martini
 *
 */

import java.io.DataOutputStream;
import java.io.IOException;
import java.util.Iterator;
import java.util.TreeSet;
import org.apache.bcel.classfile.Attribute;
import org.apache.bcel.classfile.ConstantPool;
import org.apache.bcel.classfile.Visitor;


public class ExceptionSafe extends Attribute {
        
    /**
     * This <code>TreeSet</code> records the program counter of the
     * instructions that do not raise the exception.
     */
    private TreeSet nothrows;

    /**
     *  This <code>String</code> contains the name of the exception
     *  the attribute refers to.
     */
    private String exceptionName;

    /**
     *  The index, in the Constant Pool, of the CONSTANT_Class_info
     *  structure describing the class of the considered exception.
     */
    private short exceptionNameIndex;

    public ExceptionSafe( short name_index, 
			  ConstantPool cp, 
			  short exceptionNameIndex) {
	super(Constants.TAG_EXCEPTIONSAFE, name_index, 4, cp);
	nothrows = new TreeSet();
	this.exceptionNameIndex = exceptionNameIndex;
	this.exceptionName = cp.getConstantString(exceptionNameIndex, 
					    org.apache.bcel.Constants.CONSTANT_Class).toString();
    }
    
    public final void dump(DataOutputStream file) throws IOException {
	if (getLength()!=((2*nothrows.size())+4)) {
	     // consistency check
	    throw new IOException("The attribute size is not consistent with the nembers of pc's specified.");
	}
	super.dump(file);
	file.writeShort(exceptionNameIndex);
	file.writeShort(nothrows.size());
	for (Iterator i = nothrows.iterator(); i.hasNext();) {
	    Integer pc = (Integer) i.next();
	    file.writeShort(pc.shortValue());
	}
    }

    public final boolean isSafe(int i) {
	return nothrows.contains(new Integer(i));
    }
    
    public final boolean addPc(int i) {
	boolean b = nothrows.add(new Integer(i));
	if (b) {
	    setLength(getLength()+2);
	}
	return b;
    }
 
    public String toString() {
	return ("ExceptionSafe["+exceptionName+"]");
    }

    /** Stub method to satisfy the contract of
     * <code>Attribute</code>*/
    public Attribute copy(ConstantPool constant_pool) { 
	return null;
    }

    /** Stub method to satisfy the contract of
     * <code>Attribute</code>*/
    public void accept(Visitor v) {};

}
