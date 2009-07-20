package checkingIF;
/*
 * Created on Jan 25, 2005
 * @version $Id: State.java,v 1.1 2005/02/02 14:40:10 lmartini Exp $
 */

/**
 * @author Luca Martini
 * 
 *  a state of the abstract interpreter
 */

import embeddingInfo.HL;
import embeddingInfo.SecLevel;
import java.util.HashMap;
import java.util.Set;
import java.util.Iterator;
import org.apache.bcel.generic.Instruction;
import org.apache.bcel.generic.InstructionList;
import org.apache.bcel.generic.MethodGen;


public class State {
    private OpStack stack;
    private SecEnv se;

    /**
     * Get the Stack value.
     * @return the Stack value.
     */
    public OpStack getStack() {
	return stack;
    }


    /**
     * Get the security environment value.
     * @return the Se value.
     */
    public SecEnv getSe() {
	return se;
    }

    public State(MethodGen m, SecLevel sl) {
	stack  = new OpStack(m.getMaxStack());
	se = new SecEnv(m,sl);
    }

    public State(SecEnv se, OpStack stack){
	this.se = se;
	this.stack = stack;
    }
    
    protected Object clone(){
	State s = new State(se.getClone(), stack.getClone());
	return s;
    }

    public State getClone(){
	return (State) clone();
    }
    
    public boolean equals(Object o){
	if (!(o instanceof State)) return false; // implies "null" is non-equal.
	State f = (State) o;
	return this.stack.equals(f.stack) && this.se.equals(f.se);
    }
    
    /**
     * Returns a String representation of the State instance.
     */
    public String toString(){
	String s= "OperandStack:";
	s += stack;
	s += "Security Environment:\n";
	s += se;
	
	return s;
    }

}