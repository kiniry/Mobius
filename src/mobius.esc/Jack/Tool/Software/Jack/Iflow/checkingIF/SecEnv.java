package checkingIF;
/*
 * Created on Jan 25, 2005
 * @version $Id: SecEnv.java,v 1.3 2005/02/17 12:46:10 lmartini Exp $
 */

/**
 * @author Luca Martini
 * 
 *  the security environment for instructions
 */

import embeddingInfo.HL;
import embeddingInfo.SecLevel;
import java.util.Arrays;
import java.util.HashMap;
import java.util.Iterator;
import java.util.Set;
import org.apache.bcel.generic.Instruction;
import org.apache.bcel.generic.InstructionHandle;
import org.apache.bcel.generic.InstructionList;
import org.apache.bcel.generic.MethodGen;

public class SecEnv {

    /** We hold the levels information here. 
	An array could be used to gain space.
	Key: InstructionHandle, Value: SecLevel*/
    private HashMap map;

    /** The numbers of instruction */
    private int ninstr;

    /**
     * Creates an empty stack with a maximum of maxStack slots.
     */
    private SecEnv(int instrs){
	this.map = new HashMap(instrs,1);
	this.ninstr = instrs;
    }
    
    private SecEnv(){
    }

    /**
     * Returns a deep copy of this object; that means, the clone operates
     * on a new stack. However, the SecLevel objects on the stack are
     * shared.
     */
    protected Object clone(){
	SecEnv se = new SecEnv();
	se.ninstr = this.ninstr;
	se.map = (HashMap) this.map.clone();
	return se;
    }

    /**
     * Returns true if and only if this OpStack
     * equals another, meaning equal lengths and equal
     * objects on the stacks.
     */
    public boolean equals(Object o){
	if ((!(o instanceof SecEnv))|| (o == null)) return false;
	SecEnv s = (SecEnv) o;
	return this.map.equals(s.map);
    }

    /**
     * Returns a (typed!) clone of this.
     *
     * @see #clone()
     */
    public SecEnv getClone(){
	return (SecEnv) this.clone();
    }

    /**
     * Returns the security level of the Instruction passed as parameter.
     */
    public SecLevel get(InstructionHandle ih){
	return (SecLevel)(map.get(ih));
    }

  
    /**
     * Returns a String representation of this SecEnv instance.
     */
     public String toString(){
 	String s = "";
	Object[] keys = map.keySet().toArray();
	Arrays.sort(keys,new IHComparator());
	for (int i = 0; i < keys.length; i++) {
	    s += map.get(keys[i])+"\t"+keys[i]+"\t"+"\n";
	}
	return s;
     }

//     public String toString2(){
// 	String s = "";
// 	Set keys = map.keySet();
// 	for (Iterator i = keys.iterator(); i.hasNext();) {
// 	    InstructionHandle ih = (InstructionHandle) (i.next());
// 	    s += map.get(ih)+"\t"+ih+"\t"+"\n";
// 	}
	
// 	return s;
//     }

    /**
     * Merges another stack secEnv into this instance's state.
     */
    public void merge(SecEnv s) {
	for (Iterator j = map.keySet().iterator(); j.hasNext();) { 
	    InstructionHandle i = (InstructionHandle) j.next();
	    map.put(i, ((SecLevel) s.map.get(i)));
	}
    }
    
    
    /**
     * <code>getInstructions</code> serves only as debugging function.
     *
     * @return the <code>Set</code> of instructions of the method the
     * Map is related to
     */
    public Set getInstructions() {
	return map.keySet();
    }
    
    /** 
     * <code>lift</code> method upgrades the security levels of the
     * instructions in a set with a new level that is the least upper
     * bound between the old level and a level passed as parameter.
     *
     * @param sl the <code>SecLevel</code> value to use to compute the lub 
     * @param is the <code>Set</code> of instructions involved in the
     * lift.
     */
    public void lift(SecLevel sl, Set is) {
	for (Iterator it = is.iterator(); it.hasNext();) {
	    InstructionHandle ih = (InstructionHandle) it.next();
	    ((SecLevel) (map.get(ih))).sup(sl);
	}
    }	
    
    public SecEnv(MethodGen m, SecLevel sl) {
	InstructionList il = m.getInstructionList();
	this.ninstr = il.size();
	this.map = new HashMap(ninstr,1);
	Iterator i = il.iterator();
	while (i.hasNext()) {
	    map.put((InstructionHandle)(i.next()), (SecLevel) sl.clone());
	   
	}
    }
    
    // only for testing
    public static void main(String[] args) {
	// to be tested
    }
}

