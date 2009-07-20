package checkingIF;

/* ====================================================================
 * The Apache Software License, Version 1.1
 *
 * Copyright (c) 2001 The Apache Software Foundation.  All rights
 * reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions
 * are met:
 *
 * 1. Redistributions of source code must retain the above copyright
 *    notice, this list of conditions and the following disclaimer.
 *
 * 2. Redistributions in binary form must reproduce the above copyright
 *    notice, this list of conditions and the following disclaimer in
 *    the documentation and/or other materials provided with the
 *    distribution.
 *
 * 3. The end-user documentation included with the redistribution,
 *    if any, must include the following acknowledgment:
 *       "This product includes software developed by the
 *        Apache Software Foundation (http://www.apache.org/)."
 *    Alternately, this acknowledgment may appear in the software itself,
 *    if and wherever such third-party acknowledgments normally appear.
 *
 * 4. The names "Apache" and "Apache Software Foundation" and
 *    "Apache BCEL" must not be used to endorse or promote products
 *    derived from this software without prior written permission. For
 *    written permission, please contact apache@apache.org.
 *
 * 5. Products derived from this software may not be called "Apache",
 *    "Apache BCEL", nor may "Apache" appear in their name, without
 *    prior written permission of the Apache Software Foundation.
 *
 * THIS SOFTWARE IS PROVIDED ``AS IS'' AND ANY EXPRESSED OR IMPLIED
 * WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES
 * OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
 * DISCLAIMED.  IN NO EVENT SHALL THE APACHE SOFTWARE FOUNDATION OR
 * ITS CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
 * SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
 * LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF
 * USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND
 * ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY,
 * OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT
 * OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF
 * SUCH DAMAGE.
 * ====================================================================
 *
 * This software consists of voluntary contributions made by many
 * individuals on behalf of the Apache Software Foundation.  For more
 * information on the Apache Software Foundation, please see
 * <http://www.apache.org/>.
 */

import embeddingInfo.ExceptionSafe;
import embeddingInfo.IHComparator;
import exc.GeneralCheckingError;
import exc.TypeCheckError;
import java.util.ArrayList;
import java.util.BitSet;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Hashtable;
import java.util.Iterator;
import java.util.Set;
import java.util.TreeSet;
import org.apache.bcel.Repository;
import org.apache.bcel.classfile.Attribute;
import org.apache.bcel.classfile.JavaClass;
import org.apache.bcel.classfile.Method;
import org.apache.bcel.generic.ATHROW;
import org.apache.bcel.generic.BranchInstruction;
import org.apache.bcel.generic.ConstantPoolGen;
import org.apache.bcel.generic.ExceptionThrower;
import org.apache.bcel.generic.GETFIELD;
import org.apache.bcel.generic.GotoInstruction;
import org.apache.bcel.generic.Instruction;
import org.apache.bcel.generic.InstructionHandle;
import org.apache.bcel.generic.InstructionList;
import org.apache.bcel.generic.JsrInstruction;
import org.apache.bcel.generic.MethodGen;
import org.apache.bcel.generic.PUTFIELD;
import org.apache.bcel.generic.RET;
import org.apache.bcel.generic.ReturnInstruction;
import org.apache.bcel.generic.Select;
import org.apache.bcel.verifier.structurals.ExceptionHandler;
import org.apache.bcel.verifier.structurals.ExceptionHandlers;
import org.apache.bcel.verifier.structurals.Subroutine;
import org.apache.bcel.verifier.structurals.Subroutines;


/**
 * This class represents a control flow graph of a method. And
 * contains all the structures needed to perform an abstract execution
 *
 * @version $Id: ControlFlowGraph.java,v 1.5 2005/03/24 10:28:29 lmartini Exp $
 * @author Luca Martini
 */
public class ControlFlowGraph{
    private boolean debug = false;
    private boolean withExceptions = true;
    /**
     * Objects of this class represent a node in a ControlFlowGraph.
     * These nodes are instructions, not basic blocks.
     */
    private class InstructionContext implements ICInterface{
	/* The Instruction this InstructionContext is wrapped around.   */
	private InstructionHandle instruction;
	
	/**
	 * The 'incoming' execution Frames.
	 */
	private HashMap beforeStates;	// key: the last-executed JSR
	
	/**
	 * The 'outgoing' execution Frames.
	 */
	private HashMap afterStates; // key: the last-executed JSR 
	
	/**
	 * the after state for exceptions
	 *
	 */
	private State excState;

	/**
	 * The 'execution predecessors' - a list of type InstructionContext 
	 * of those instances that have been execute()d before in that order.
	 */
	private ArrayList executionPredecessors = null; // Type: InstructionContext
	
	/**
	 * The set of Postdominators expressed as a bit vector (see Dragon Book, p.161)
	 *
	 */
	private BitSet pdoms;

	/**
	 * The position occupied by the instruction in the bit vector
	 * (it is set to the position occupiendin the InstructionList)
	 *
	 */
	private int position;
	
	private InstructionHandle[] succs; // the successors of the instruction

	/**
	 * This immediate postdominator field is only meaningful for branch instructions
	 */
	private InstructionHandle ipd = null;

	/**
	 * Creates an InstructionHandleImpl object from an InstructionHandle.
	 * Creation of one per InstructionHandle suffices. Don't create more.
	 */
	public InstructionContext(InstructionHandle inst, int pos){
	    if (inst == null) throw new GeneralCheckingError("Cannot instantiate InstructionContext from NULL.");
	    instruction = inst;
	    beforeStates = new java.util.HashMap();
	    afterStates = new java.util.HashMap();
	    pdoms = new BitSet(ninstr);
	    pdoms.set(0,ninstr);
	    position = pos;
	}
	
	public InstructionContext() { // constructor for the fake end node 
	    instruction = null;
	    pdoms = new BitSet(ninstr);
	    pdoms.set(ninstr-1);
	    position = ninstr-1;
	    succs = new InstructionHandle[0];
	}
	
	/**
	 * Returns the exception handlers of this instruction.
	 */
	public ExceptionHandler[] getExceptionHandlers(){
	    return exceptionhandlers.getExceptionHandlers(getInstruction());
	}
	
	/**
	 * Returns a clone of the "outgoing" frame situation with
	 * respect to the given ExecutionChain.
	 */	
	public State getAfterState(ArrayList execChain){
	    executionPredecessors = execChain;
	    
	    State org;

	    InstructionContext jsr = lastExecutionJSR();
	    org = (State) afterStates.get(jsr);
	    if (org == null){
		throw new GeneralCheckingError("AfterState  not set! This:\n"+this+"\nExecutionChain: "+getExecutionChain()+"\nAfterStates: '"+afterStates+"'.");
	    }
	    return org.getClone();
	}

	public State getExcState(){
	    if (excState == null) 
		return null;
	    return excState.getClone();
	}

	/**
	 * @return true - if and only if the "outgoing" frame situation
	 * changed from the one before execute()ing.
	 */
	public boolean execute(State beforeState, ArrayList execPreds, CheckingVisitor vis, ExceptionVisitor ev){
	    InstructionHandle currIns = getInstruction();
	    executionPredecessors = (ArrayList) execPreds.clone();
	    
	    //sanity checks
	    if ( (lastExecutionJSR() == null) && (subroutines.subroutineOf(currIns) != subroutines.getTopLevel() ) ){
		throw new GeneralCheckingError("Huh?! Am I '"+this+"' part of a subroutine or not?");
	    }
	    if ( (lastExecutionJSR() != null) && (subroutines.subroutineOf(currIns) == subroutines.getTopLevel() ) ){
		throw new GeneralCheckingError("Huh?! Am I '"+this+"' part of a subroutine or not?");
	    }
	    
	    State bs = (State) beforeStates.get(lastExecutionJSR());
	    if (bs == null){// no incoming frame was set, so set it.
		beforeStates.put(lastExecutionJSR(), beforeState);
		bs = beforeState;
	    } else {// if there was an "old" beforeState
		if (bs.equals(beforeState)){ //shortcut: no need to merge equal frames.
		    return false;
		}
		if (! mergeBeforeStates(beforeState)){
		    return false;
		}
	    }
	    
	    // Now we're sure the beforeState has changed!
			
	    // new before_states is already merged in, see above. 
	    State workingState = bs.getClone();

	    
	    // This executes the Instruction.
	    // Therefore the workingFrame object is modified.
	    
	    vis.setState(workingState, currIns);
	    log("Abstractly executing "+currIns);
	    log("Execution Chain      "+execPreds);
	    log("BeforeState "+workingState);
	   
	    try {
		currIns.accept(vis);
			       
	    } catch (TypeCheckError e) {
		e.extendMessage("","\nInstruction: "+currIns+
				"\nAbstract State\n"+workingState);
		extendMessageWithFlow(e);
		throw e;
	    }
	    afterStates.put(lastExecutionJSR(), workingState);
	    log("AfterState "+workingState);
	    
	    // possibly create exceptional afterstates!!
	    ev.setState(bs.getClone(), currIns);
	    currIns.accept(ev);
	    if (ev.hasExceptions) {
		excState = ev.getState();
	    }
	    
	    
	    // new before state was different from old inFrame so merging them
	    // yielded a different this.inFrame.
	    return true;	
	}
	
	/**
	 * Returns a simple String representation of this InstructionContext.
	 */
	public String toString(){
	    //TODO: Add additional, e.g.  Is this an
	    //ExceptionHandler? Is this a RET? Is this the start of a
	    //subroutine?
	    String ret = getInstruction().toString(false);
	    return ret;
	}
	
	/**
	 * Does the actual merging (vmspec2, page 146).  Returns true
	 * IFF the current before state was changed in course of merging with
	 * the state beforeState.
	 */
	private boolean mergeBeforeStates(State beforeState){
	    // TODO: Can be performance-improved.
	    // move to State.java
	    State bs = (State) beforeStates.get(lastExecutionJSR());
	    OpStack oldstack = bs.getStack().getClone();
	    SecEnv oldse = bs.getSe().getClone();
	    bs.getStack().merge(beforeState.getStack());
	    bs.getSe().merge(beforeState.getSe());
	    
	    if (oldstack.equals(bs.getStack()) &&
		oldse.equals(bs.getSe()) ){
		return false;
	    }
	    else
		return true;
	}
	
	/**
	 * Returns the control flow execution chain. This is built
	 * while execute(Frame, ArrayList)-ing the code represented
	 * by the surrounding ControlFlowGraph.
	 */
	private String getExecutionChain(){
	    String s = this.toString();
	    for (int i=executionPredecessors.size()-1; i>=0; i--){
		s = executionPredecessors.get(i)+"\n" + s;
	    }
	    return s;
	}
	
	
	/**
	 * Extends the TypeCheckError exception ("e") object with an
	 * at-the-end-extended message.  This extended message will
	 * then reflect the execution flow needed to get to the
	 * constraint violation that triggered the throwing of the "e"
	 * object.
	 */
	private void extendMessageWithFlow(TypeCheckError e){
	    String s = "Execution flow:\n";
	    e.extendMessage("", s+getExecutionChain());
	}

	public InstructionHandle getInstruction(){
	    return instruction;
	}

	/**
	 * Returns the InstructionContextImpl with an JSR/JSR_W
	 * that was last in the ExecutionChain, without
	 * a corresponding RET, i.e.
	 * we were called by this one.
	 * Returns null if we were called from the top level.
	 */
	private InstructionContext lastExecutionJSR(){
	    
	    int size = executionPredecessors.size();
	    int retcount = 0;
	    
	    for (int i=size-1; i>=0; i--){
		InstructionContext current = (InstructionContext) (executionPredecessors.get(i));
		Instruction currentlast = current.getInstruction().getInstruction();
		if (currentlast instanceof RET) retcount++;
		if (currentlast instanceof JsrInstruction){
		    retcount--;
		    if (retcount == -1) return current;
		}
	    }
	    return null;
	}
	
	/* Satisfies InstructionContext.getSuccessors(). */
	public ICInterface[] getSuccessors(){
	    return contextsOf(_getSuccessors());
	}
	
	/**
	 * A utility method that calculates the successors of a given
	 * Instruction That means, a RET does have successors as
	 * defined here.  A JsrInstruction has its target as its
	 * successor (opposed to its physical successor) as defined
	 * here.
	 */
	// TODO: implement caching!
	private InstructionHandle[] _getSuccessors(){
	    final InstructionHandle[] empty = new InstructionHandle[0];
	    final InstructionHandle[] single = new InstructionHandle[1];
	    final InstructionHandle[] pair = new InstructionHandle[2];
		
	    Instruction inst = getInstruction().getInstruction();
	    
	    if (inst instanceof RET){
		Subroutine s = subroutines.subroutineOf(getInstruction());
		
		InstructionHandle[] jsrs = s.getEnteringJsrInstructions();
		InstructionHandle[] ret = new InstructionHandle[jsrs.length];
		for (int i=0; i<jsrs.length; i++){
		    ret[i] = jsrs[i].getNext();
		}
		return ret;
		
	    }
	    
	    // Terminates method normally.
	    if (inst instanceof ReturnInstruction){
		return empty;
	    }
	    
	    // Terminates method abnormally, because JustIce mandates
	    // subroutines not to be protected by exception handlers.
	    if (inst instanceof ATHROW){
		return empty;
	    }
	    
	    // See method comment.
	    if (inst instanceof JsrInstruction){
		single[0] = ((JsrInstruction) inst).getTarget();
		return single;
	    }

	    if (inst instanceof GotoInstruction){
		single[0] = ((GotoInstruction) inst).getTarget();
		return single;
	    }
	    
	    if (inst instanceof BranchInstruction){
		if (inst instanceof Select){
		    // BCEL's getTargets() returns only the
		    // non-default targets, thanks to Eli Tilevich for
		    // reporting.
		    InstructionHandle[] matchTargets = ((Select) inst).getTargets();
		    InstructionHandle[] ret = new InstructionHandle[matchTargets.length+1];
		    ret[0] = ((Select) inst).getTarget();
		    System.arraycopy(matchTargets, 0, ret, 1, matchTargets.length);
		    return ret;
		}
		else{
		    pair[0] = getInstruction().getNext();
		    pair[1] = ((BranchInstruction) inst).getTarget();
		    return pair;
		}
	    }
	    
	    // default case: Fall through.		
	    single[0] = getInstruction().getNext();
	    return single;
	}

	
	/**
	 * Calculates the control region of an instructionContext
	 *
	 * @return a <code>Set</code> of InstructionHandle
	 */
	public Set region() {
	    TreeSet ret = new TreeSet(new IHComparator());
	    if (succs.length <= 1)
		// for sequential instructions the region is empty
		return ret;
	    BitSet bs = new BitSet(ninstr); // used for graph coloring
	    // mark the ipd as visited
	    bs.set(getPosition(ipd));
	    _region(this,ret,bs);
	    
	    return ret;
	}

	private void _region(InstructionContext ic, Set s, BitSet bs) {
	    // if the node has not been visited yet and it is not the ipd
	    if (!bs.get(ic.position)) {
		// mark the node
		bs.set(ic.position);
		s.add(ic.getInstruction());
		for (int i = 0; i < ic.succs.length; i++) {
		    if (ic.succs[i] == null) {
			_region(endNode, s, bs);
		    } else {
			_region(contextOf(ic.succs[i]), s, bs);
		    }
		}
	    }
	}
	
    } // End Inner InstructionContext Class.
    
    /** The MethodGen object we're working on. */
    private final MethodGen method_gen;
    
    /** The Subroutines object for the method whose control flow is
     * represented by this ControlFlowGraph. */
    private final Subroutines subroutines;
    
    /** All InstructionContext instances of this ControlFlowGraph.<br> 
	keys: InstructionHandle, values: InstructionContext*/
    private Hashtable instructionContexts = new Hashtable(); //
    
    private InstructionContext endNode;

    /** The ExceptionHandlers object for the method whose control flow
     * is represented by this ControlFlowGraph. */
    public final ExceptionHandlers exceptionhandlers;
    
    /**
     * The number of instructions in the method + 1 (the end node)
     *
     */
    private int ninstr;

    /**
     * The set of <code>ExceptionSafe</code> attributes associated
     * with this method.
     *
     * @see embeddingInfo.ExceptionSafe
     */
    private Set esAttributes;

    /** 
     * A Control Flow Graph.
     */
    public ControlFlowGraph(MethodGen method_gen, boolean _debug){
	this.debug = _debug;
	subroutines = new Subroutines(method_gen);
	exceptionhandlers = new ExceptionHandlers(method_gen);
	
	InstructionHandle[] instructionhandles = method_gen.getInstructionList().getInstructionHandles();
	ninstr = instructionhandles.length+1;// the end node
	for (int i=0; i<instructionhandles.length; i++){
	    instructionContexts.put(instructionhandles[i], new InstructionContext(instructionhandles[i],i));
	}
	
	endNode = new InstructionContext();
	
	this.method_gen = method_gen;
	
	/* various initializations*/
	parseExceptionSafe();
	computeSuccessors();
	computePD();
	computeIPD();
	if (debug) 
	    printPD();
    }

    private final void parseExceptionSafe(){
	esAttributes = new HashSet();
	Attribute[] attrs = method_gen.getMethod().getAttributes();
	for (int i = 0; i < attrs.length; i++) {
	    if (attrs[i] instanceof ExceptionSafe) {
		esAttributes.add(attrs[i]);
	    }
	}
    }

    private void printPD() {
	for (Iterator i = instructionContexts.values().iterator(); i.hasNext();) {
	    InstructionContext ic = (InstructionContext) i.next();
	    System.out.print("["+ic.position+"] "+ic.getInstruction()+ " -> " + ic.pdoms);
	    System.out.print(" successors: ");
	    for (int j = 0; j < ic.succs.length; j++) {
		if (ic.succs[j] == null) {
		    System.out.println("END ");
		} else {
		    System.out.print(ic.succs[j].getPosition() + " ");
		}
		
	    }
	    if (ic.succs.length>1) {
		System.out.print("\nIPD = " + ic.ipd + "\nRegion \n");
		Set reg = ic.region();
		for (Iterator j = reg.iterator(); j.hasNext();) {
		    System.out.println((InstructionHandle) j.next());
		}
	    }
	    System.out.println();
	}
	System.out.println("END -> "+endNode.pdoms);
    }

    private void computeSuccessors() {
	for (Iterator i = instructionContexts.values().iterator(); i.hasNext();) {
	    InstructionContext ic = (InstructionContext) i.next();
	    InstructionHandle instrh = ic.getInstruction();
	    Instruction instr = instrh.getInstruction();
	    
	    // we exclude return instruction because we assume no
	    // MONITOR instructions (Return instructions throws
	    // exceptions olny in case of illegal monitor state).
	    if ((instr instanceof ExceptionThrower) &&
		(!(instr instanceof ReturnInstruction)) &&
		(!isSafe(instrh))) {
		ExceptionHandler[] ehs = exceptionhandlers.getExceptionHandlers(ic.getInstruction());
		// we assume here that there is only a type of Exception
		InstructionHandle[] succs = new InstructionHandle[2];
		succs[0] = ic.getInstruction().getNext();
		switch (ehs.length) {
		case 0: // exception not handled in the method, add the end point to the successor
		    succs[1] = null;
		    break;
		case 1:
		    succs[1] = ehs[0].getHandlerStart();
		    break;
		default:
		    throw new GeneralCheckingError("Every Instruction must be protected at most by one handler!.");
		}
		ic.succs = succs;
	    }
	    else {
		ic.succs = ic._getSuccessors();
	    }
	}
    }
    
    /** 
     *
     *   please comment me!
     *
     */
    private boolean isSafe(InstructionHandle ih) {
	int offset = ih.getPosition();	
	for (Iterator i = esAttributes.iterator(); i.hasNext();) {
	    ExceptionSafe es = (ExceptionSafe)(i.next());
	    if (es.isSafe(offset)) {
		return true;
	    }
	}
	return false;

    }

    private void computeIPD() {
	InstructionHandle[] ihs = method_gen.getInstructionList().getInstructionHandles();
	for (Iterator it = instructionContexts.values().iterator(); it.hasNext();) {
	    InstructionContext ic = (InstructionContext) it.next();
	    if (ic.succs.length > 1) { // only for branch instructions 
		//System.out.println("searching IPD("+ic+")");
		for(int i=ic.pdoms.nextSetBit(0); i>=0; i=ic.pdoms.nextSetBit(i+1)) {
		    // i is the ipd candidate, let see if it meets the conditions
		    //System.out.println("Candidate "+i);
		    boolean isIpd = true;
		    for(int j=ic.pdoms.nextSetBit(0); j>=0; j=ic.pdoms.nextSetBit(j+1)) {
			// the postdominators of the ipd candidate 
			BitSet bs;
			if (i==ihs.length) 
			    bs = endNode.pdoms; 
			else 
			    bs = contextOf(ihs[i]).pdoms ;
			//System.out.println(bs);
			
			if ((j!=i)&&(!bs.get(j))) {
			    isIpd = false;
			    break;
			}
		    }
		    if (isIpd) {
			//System.out.println("FOUND");
			if (i!=ihs.length) 
			    ic.ipd = ihs[i];
			break;
		    }
		    else continue;		       
		}
	    }
	}
    }
    
    /**
     * <code>computePD</code> builds the set of postdominators as
     * specified in Aho, Sethi, Ullman book
     *
     */
    private void computePD() {
	boolean modified = true;
	int iter=0;
	while (modified) {
	    modified = false;
	    // the end node
	    for (Iterator i = instructionContexts.values().iterator(); i.hasNext();) {
		InstructionContext ic = (InstructionContext) i.next();
		BitSet nbs = new BitSet(ninstr);
		nbs.set(0,ninstr);
		for (int j = 0; j < ic.succs.length; j++) {
		    InstructionContext successor;
		    if (ic.succs[j] == null) {
			successor = endNode;
		    }
		    else {
			successor = contextOf(ic.succs[j]);
		    }
		    nbs.and(successor.pdoms);
		}
		/* TODO: change this check making the getsuccessor
		 * return null for a successor of return
		 * instruction */
		if (ic.getInstruction().getInstruction() instanceof ReturnInstruction) {
		    // in this case succs.length == 0
		    nbs.and(endNode.pdoms);
		}
		
		nbs.set(ic.position);
		if (!(nbs.equals(ic.pdoms))) {
		    modified = true;
		    ic.pdoms = nbs;
		}
	    }
	}
	// Removing self-postdominance
	for (Iterator i = instructionContexts.values().iterator(); i.hasNext();) {
 	    InstructionContext ic = (InstructionContext) i.next();
	    ic.pdoms.clear(ic.position);
 	}
    }
    
    
    /**
     * Returns the InstructionContext of a given instruction.
     */
    public  InstructionContext contextOf(InstructionHandle inst){
	InstructionContext ic = (InstructionContext) instructionContexts.get(inst);
	if (ic == null)
	    throw new GeneralCheckingError("InstructionContext requested for an InstructionHandle that's not known!");
	return ic;
    }
    
    /**
     * Return the position of an instructionHandle in the array of instructions.
     * Works for the fake end node too.
     */
    public int getPosition(InstructionHandle inst) {
	if (inst == null) {
	    return endNode.position;
	}
	InstructionContext ic = (InstructionContext) instructionContexts.get(inst);
	return ic.position;	
    }
	
    /**
     * Returns the InstructionContext[] of a given InstructionHandle[],
     * in a naturally ordered manner.
     */
    public InstructionContext[] contextsOf(InstructionHandle[] insts){
	InstructionContext[] ret = new InstructionContext[insts.length];
	for (int i=0; i<insts.length; i++){
	    ret[i] = contextOf(insts[i]);
	}
	return ret;
    }
    
    /**
     * Returns an InstructionContext[] with all the
     * InstructionContext instances for the method whose control
     * flow is represented by this ControlFlowGraph <B>(NOT
     * ORDERED!)</B>.
     */
    public InstructionContext[] getInstructionContexts(){
	InstructionContext[] ret = new InstructionContext[instructionContexts.values().size()];
	return (InstructionContext[]) instructionContexts.values().toArray(ret);
    }
    
    /**
     * Returns true, if and only if the said instruction is not
     * reachable; that means, if it not part of this ControlFlowGraph.
     */
    public boolean isDead(InstructionHandle i){
	return instructionContexts.containsKey(i);
    }

    public Set region(InstructionHandle ih) {
	return contextOf(ih).region();
    }
    
    /**
     * Log function to print verbose output
     */
    private void log(String s) {
	if (debug)	
	    System.out.println(s);
    }

    public static void main(String[] args) {//only for testing
	JavaClass clazz = Repository.lookupClass(args[0]);
	ConstantPoolGen cpg = new ConstantPoolGen(clazz.getConstantPool());
	Method[] mlist = clazz.getMethods();
	for (int i = 0; i < mlist.length; i++) {
	    MethodGen mg = new MethodGen(mlist[i],clazz.getClassName(),cpg);
	    System.out.println("Method "+mg);
	    ControlFlowGraph cfg = new ControlFlowGraph(mg, true);
	    
	}
	
    }
    
}

