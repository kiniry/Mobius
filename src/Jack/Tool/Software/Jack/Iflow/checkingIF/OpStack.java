package checkingIF;
/*
 * Created on Jan 24, 2005
 * @version $Id: OpStack.java,v 1.2 2005/03/21 09:36:37 lmartini Exp $
 */

/**
 * @author Luca Martini
 * 
 *  the operands stack
 *  mainly borrowed from Enver Haase 
 */

import embeddingInfo.HL;
import embeddingInfo.SecLevel;
import exc.GeneralCheckingError;
import java.util.ArrayList;


public class OpStack {

    /** We hold the stack information here. */
    private ArrayList stack = new ArrayList();

    /** The maximum number of stack slots this OpStack instance may hold. */
    private int maxStack;

    /**
     * Creates an empty stack with a maximum of maxStack slots.
     */
    public OpStack(int maxStack){
	this.maxStack = maxStack;
    }

    /**
     * Returns a deep copy of this object; that means, the clone operates
     * on a new stack. However, the SecLevel objects on the stack are
     * shared.
     */
    protected Object clone(){
	OpStack newstack = new OpStack(this.maxStack);
	newstack.stack = (ArrayList) this.stack.clone();
	return newstack;
    }

    /**
     * Clears the stack.
     */
    public void clear(){
	stack = new ArrayList();
    }

    /**
     * Returns true if and only if this OpStack
     * equals another, meaning equal lengths and equal
     * objects on the stacks.
     */
    public boolean equals(Object o){
	if (!(o instanceof OpStack)) return false;
	OpStack s = (OpStack) o;
	return this.stack.equals(s.stack);
    }

    /**
     * Returns a (typed!) clone of this.
     *
     * @see #clone()
     */
    public OpStack getClone(){
	return (OpStack) this.clone();
    }

    /**
     * Returns true IFF this OpStack is empty.
     */
    public boolean isEmpty(){
	return stack.isEmpty();
    }

    /**
     * Returns the number of stack slots this stack can hold.
     */
    public int maxStack(){
	return this.maxStack;
    }

    /**
     * Returns the element on top of the stack. The element is not popped off the stack!
     */
    public SecLevel peek(){
	return peek(0);
    }

    /**
     * Returns the element that's i elements below the top element; that means,
     * iff i==0 the top element is returned. The element is not popped off the stack!
     */
    public SecLevel peek(int i){
	return (SecLevel) stack.get(size()-i-1);
    }

    /**
     * Returns the element on top of the stack. The element is popped off the stack.
     */
    public SecLevel pop(){
	SecLevel e = (SecLevel) stack.remove(size()-1);
	return e;
    }

    /**
     * Pops i elements off the stack. ALWAYS RETURNS "null"!!!
     */
    public SecLevel pop(int i){
	for (int j=0; j<i; j++){
	    pop();
	}
	return null;
    }

    /**
     * Pushes a SecLevel object onto the stack.
     */
    public void push(SecLevel sl) {
	SecLevel sl_copy = (SecLevel) sl.clone();
	stack.add(sl_copy);
    }

    /**
     * Returns the size of this OpStack; that means, how many SecLevel objects there are.
     */
    int size(){
	return stack.size();
    }

    /**
     * Returns a String representation of this OpStack instance.
     */
    public String toString(){
	String s = "";
	for (int i=0; i<size(); i++){
	    s+=peek(i);
	}
	s+=" MaxStack: "+maxStack+"\n";
	return s;
    }

    /**
     * Merges another stack state into this instance's stack state.
     */
    public void merge(OpStack s) {
	if (size()!=s.size()) {
	    throw new GeneralCheckingError("Merging stacks of different lengths");
	}
	int slength = size();
	for (int i=0; i<slength; i++) {// sup
	    SecLevel sl1 = (SecLevel) stack.get(i);
	    SecLevel sl2 = (SecLevel) s.stack.get(i);
	    
	    if ((sl1.isArray != sl2.isArray) || 
		((sl1.isArray) && (sl1.levelArray != sl2.levelArray))){
		throw new GeneralCheckingError("Merging not compatible stacks: s1=\""+this+"\", s2=\""+s+"\".");
	    }
	    stack.set(i, sl1.lub(sl2));
	}
    }

    public void lift(SecLevel sl) {
	for (int i=0; i<size(); i++) // sup
	    stack.set(i, ((SecLevel)(stack.get(i))).lub(sl));
    }


    // only for testing
    public static void main(String[] args) {
	OpStack s1 = new OpStack(10), s2 = new OpStack(10), s3;
	HL sl = new HL("L",true);
	HL sl1 = new HL("H",true);
	sl1.levelArray = HL.L;
	try {
	    s1.push(sl);
	    s1.push(sl);
	    s2.push(sl1);
	    s2.push(sl);
	    System.out.println("s1 " + s1);
	    System.out.println("s2 " + s2);
	    s3 = s1.getClone();
	    System.out.println("s3 " + s3);
	    s1.merge(s2);
	    System.out.println("s3 " + s3);

	    System.out.println("s1 sup s2 " + s1);
	    s1.push(sl.top());
	    System.out.println("s1 " + s1);
	    System.out.println("s3 " + s3);
	    s3.lift(sl);
	    System.out.println("s3 " + s3);
	    s3.lift(sl.top());
	    System.out.println("s3 " + s3);
	    s1.merge(s2);
	    System.out.println("s1 sup s2 " + s1);
	 
	} catch (Exception e) {
	    System.out.println(e.getMessage());
	    return;
	}
	
    }
    
}

