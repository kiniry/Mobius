package checkingIF;
/*
 * Created on Jan 21, 2005
 * @version $Id: IFVerifier.java,v 1.4 2005/03/21 09:36:37 lmartini Exp $
 */

/**
 * @author Luca Martini
 * 
 */

import embeddingInfo.AbstractSecLevelMethod;
import embeddingInfo.Constants;
import embeddingInfo.HL;
import embeddingInfo.SLFieldAttributeReader;
import embeddingInfo.SLMethodAttributeReader;
import embeddingInfo.SecLevel;
import exc.GeneralCheckingError;
import exc.TypeCheckError;
import exc.VerificationException;
import java.util.ArrayList;
import java.util.Vector;
import org.apache.bcel.Repository;
import org.apache.bcel.classfile.Attribute;
import org.apache.bcel.classfile.ConstantPool;
import org.apache.bcel.classfile.Field;
import org.apache.bcel.classfile.FieldOrMethod;
import org.apache.bcel.classfile.JavaClass;
import org.apache.bcel.classfile.Method;
import org.apache.bcel.generic.ConstantPoolGen;
import org.apache.bcel.generic.InstructionHandle;
import org.apache.bcel.generic.InstructionList;
import org.apache.bcel.generic.MethodGen;
import org.apache.bcel.generic.ReturnaddressType;
import org.apache.bcel.verifier.structurals.ExceptionHandler;
import embeddingInfo.ExceptionSafeAttributeReader;




/**
 * Describe class <code>IFVerifier</code> here.
 *
 * @author <a href="mailto:">Luca Martini</a>
 * @version 1.0
 */
public class IFVerifier {
    boolean debug = false;
    JavaClass clazz;
    private ConstantPoolGen cpg;
    /**
     * The number of methods anlysed. (Each distinct
     * <code>SecLevelMethod</code> attribute contribute to the total.
     *
     */
    int numberVerified=0;
    
    /**
     * The security level <code>_sl</code> identify the non-abstract
     * class of security levels used; *
     */
    protected static SecLevel _sl = new HL();
    
    
    private static final class WorkingList{
	// InstructionContexts
	private Vector ics = new Vector(); 
	// Execution Chains, Type: ArrayList (of InstructionContext)
	private Vector ecs = new Vector(); 
	public void add(ICInterface ic, ArrayList executionChain){
	    ics.add(ic);
	    ecs.add(executionChain);
	}
	public boolean isEmpty(){
	    return ics.isEmpty();
	}
	
	public void remove(){
	    this.remove(0);
	}
	
	public void remove(int i){
	    ics.remove(i);
	    ecs.remove(i);
	}
	
	public ICInterface getIC(int i){
	    return (ICInterface) ics.get(i);
	}
	
	public ArrayList getEC(int i){
	    return (ArrayList) ecs.get(i);
	}
	
	public int size(){
	    return ics.size();
	}
    } 
    
    private void log(String s) {
	if (debug) 
	    System.out.println(s);
    }

    public IFVerifier (String s) throws VerificationException {
        clazz = Repository.lookupClass(s
				       );
	if (clazz == null) 
	    throw new GeneralCheckingError("Class "+ s +" not found in your classpath.\n");
    }
    
    private static void usage() {
	System.out.println("IFVerifier: an information checker for Java files.");
	System.out.println("$Id: IFVerifier.java,v 1.4 2005/03/21 09:36:37 lmartini Exp $");
	System.out.println("usage: java IFVerifier [-v] ClassFile");
	System.out.println("       where the -v switch adds verbose information to standard output");
	System.out.println("       and ClassFile is the class file to be verified.");
    }
        
    
    public static void main(String[] args) throws Exception{

	IFVerifier ifv;
	
	/*
	 * Registering the AttributeReaders. 
	 */
	Attribute.addAttributeReader
	    ("SecLevelField", new SLFieldAttributeReader());
	Attribute.addAttributeReader
	    ("SecLevelMethod", new SLMethodAttributeReader());
	Attribute.addAttributeReader
	    ("ExceptionSafe", new ExceptionSafeAttributeReader());
	
	/*
	 * Flushing the caches
	 */
	GetInfo.emptyCaches();

	// Adding stub signatures
	HL[] stubs = { new HL("H"), new HL("L")};
	GetInfo.addStubSignature("java.lang.Object", stubs);

	switch (args.length) {
	case 1:
	    ifv = new IFVerifier(args[0]);
	    break;
	case 2:
	    if (args[0].equals("-v")) {
		ifv = new IFVerifier(args[1]);
		ifv.debug = true;
		break;
	    }
	default:
	    usage();
	    return;
	}
	    
	ifv.cpg = new ConstantPoolGen(ifv.clazz.getConstantPool());
	
	// dump all class information
	if (ifv.debug) {
	    System.out.println(ifv.clazz);
	}
	
	
	Method[] mlist = ifv.clazz.getMethods();
	for (int i = 0; i < mlist.length; i++) {
	    try {
		System.out.println("Analyzing Method "+mlist[i]);
		if (!ifv.verify(new MethodGen(mlist[i],
					      ifv.clazz.getClassName(),
					      ifv.cpg))) {
		    System.out.println("...No security specification found");
		}
	    } catch (VerificationException e) {
		e.extendMessage("Verification Exception in method "+mlist[i]+":\n","");
		System.out.println(e.getMessage());
		System.out.println("Verification Rejected");
		return;
	    }
	}	
	    
	System.out.println(ifv.numberVerified +" analyses performed. Verification ok!! ");
	return;
    }    

    private boolean verify(MethodGen m) {
	boolean atleastone = false;
	Attribute[] aa = m.getMethod().getAttributes();
	for (int i = 0; i < aa.length; i++) {
	    if (aa[i].getTag() == Constants.TAG_SECLEVELMETHD) {
		AbstractSecLevelMethod slm = (AbstractSecLevelMethod) aa[i];
		if (! (m.isAbstract() || m.isNative()) ) {
		    System.out.println("...implicit parameter "+slm.impl_par);
		    atleastone = true;
		    numberVerified++;
		    ControlFlowGraph cfg = new ControlFlowGraph(m,debug);
		    CheckingVisitor cv = new CheckingVisitor(m,cpg,slm.impl_par,cfg);
		    ExceptionVisitor ev = new ExceptionVisitor(cpg, slm.impl_par, cfg);
		    // Build the initial state situation for this
		    // method.  Please note that the security
		    // level of all instructions is bound to a bottom value
		    m.getInstructionList().setPositions();
		    State initialState = new State(m,_sl.bottom());
		    log(initialState.getSe().toString());
		    //log("Entry point "+m.getInstructionList().getStart().hashCode());
		   
		    circulationPump(cfg,cfg.
				    contextOf(m.getInstructionList().
					      getStart()),
				    initialState,cv,ev);
		}
	    }   
	}
	
	return atleastone;
    }
    
    private void circulationPump(ControlFlowGraph cfg, 
				 ICInterface start, 
				 State startState, CheckingVisitor cv, ExceptionVisitor ev){
	WorkingList wl = new WorkingList();
	// entry point of the method
	start.execute(startState, new ArrayList(), cv,ev);
	wl.add(start, new ArrayList());
	// LOOP!
	while (!wl.isEmpty()){
	    ICInterface u;
	    ArrayList ec;
	    // 	    log("******* Iteration "+(i++) +" *******");
	    // 	    log("wl.size()="+wl.size());
	    
	    // extraction of the first item in the working list
	    u  = wl.getIC(0);
	    ec = wl.getEC(0);
	    wl.remove(0);
			
	    ArrayList oldchain = (ArrayList) (ec.clone());
	    ArrayList newchain = (ArrayList) (ec.clone());
	    newchain.add(u);
	    /* TODO: Polyvariant analysis for SUBROUTINES!!!
	       if ((u.getInstruction().getInstruction()) instanceof RET){
	       //System.err.println(u);
	       // We can only follow _one_ successor, the one after the
	       // JSR that was recently executed.
	       RET ret = (RET) (u.getInstruction().getInstruction());
	       ReturnaddressType t = (ReturnaddressType) u.getOutFrame(oldchain).getLocals().get(ret.getIndex());
	       InstructionContext theSuccessor = cfg.contextOf(t.getTarget());
		
	       // Sanity check
	       InstructionContext lastJSR = null;
	       int skip_jsr = 0;
	       for (int ss=oldchain.size()-1; ss >= 0; ss--){
	       if (skip_jsr < 0){
	       throw new GeneralCheckingError
	       ("More RET than JSR in execution chain?!");
	       }
	       //System.err.println("+"+oldchain.get(ss));
	       if (((InstructionContext) oldchain.get(ss)).
	       getInstruction().getInstruction() instanceof 
	       JsrInstruction) {
	       if (skip_jsr == 0){
	       lastJSR = (InstructionContext) oldchain.get(ss);
	       break;
	       }
	       else
	       skip_jsr--;
	       }
	       if (((InstructionContext) oldchain.get(ss)).
	       getInstruction().getInstruction() instanceof RET)
	       skip_jsr++;
	       }
	       if (lastJSR == null){
	       throw new AssertionViolatedException("RET without a JSR before in ExecutionChain?! EC: '"+oldchain+"'.");
	       }
	       JsrInstruction jsr = (JsrInstruction) (lastJSR.getInstruction().getInstruction());
	       if ( theSuccessor != (cfg.contextOf(jsr.physicalSuccessor())) ){
	       throw new GeneralCheckingError("RET '"+u.getInstruction()+"' info inconsistent: jump back to '"+theSuccessor+"' or '"+cfg.contextOf(jsr.physicalSuccessor())+"'?");
	       }
				
	       if ((theSuccessor.execute(u.getOutFrame(oldchain), newchain, icv, ev)){
	       icq.add(theSuccessor, (ArrayList) newchain.clone());
	       }
	       }
	       else{// "not a ret"
	    */	
	    // Normal successors. Add them to the queue of successors.
	    ICInterface[] succs = u.getSuccessors();
	    for (int s=0; s<succs.length; s++){
		ICInterface v = succs[s];
		if (v.execute(u.getAfterState(oldchain), newchain, cv, ev)){
		    wl.add(v, (ArrayList) newchain.clone());
		    // update the incidental exceptional successor(s)
		    ArrayList newnewchain = (ArrayList) newchain.clone();
		    newnewchain.add(v);
		    ExceptionHandler[] handlers = cfg.exceptionhandlers.getExceptionHandlers(v.getInstruction());
		    for (int t = 0; t < handlers.length; t++) {
			ICInterface ii = cfg.contextOf(handlers[t].getHandlerStart());
			State s1 = v.getExcState();
			if ((s1!= null) && (ii.execute(s1,newnewchain, cv, ev))) {
			    wl.add(ii, (ArrayList) newnewchain.clone());  
			}
		    }
		    
		}
		
	    }
	    
	    
	    //  }// end "not a ret"
	    
	    /*
	    // Exception Handlers. Add them to the queue of successors.
	    // [subroutines are never protected; mandated by JustIce]
	    ExceptionHandler[] exc_hds = u.getExceptionHandlers();
	    for (int s=0; s<exc_hds.length; s++){
	    InstructionContext v = cfg.contextOf(exc_hds[s].getHandlerStart());
	    // TODO: the "oldchain" and "newchain" is used to determine the subroutine
	    // we're in (by searching for the last JSR) by the InstructionContext
	    // implementation. Therefore, we should not use this chain mechanism
	    // when dealing with exception handlers.
	    // Example: a JSR with an exception handler as its successor does not
	    // mean we're in a subroutine if we go to the exception handler.
	    // We should address this problem later; by now we simply "cut" the chain
	    // by using an empty chain for the exception handlers.
	    //if (v.execute(new Frame(u.getOutFrame(oldchain).getLocals(), new OperandStack (u.getOutFrame().getStack().maxStack(), (exc_hds[s].getExceptionType()==null? Type.THROWABLE : exc_hds[s].getExceptionType())) ), newchain), icv, ev){
	    //icq.add(v, (ArrayList) newchain.clone());
	    if (v.execute(new Frame(u.getOutFrame(oldchain).getLocals(), new OperandStack (u.getOutFrame(oldchain).getStack().maxStack(), (exc_hds[s].getExceptionType()==null? Type.THROWABLE : exc_hds[s].getExceptionType())) ), new ArrayList(), icv, ev)){
	    icq.add(v, new ArrayList());
	    }
	    }
	    */
	}// while (!wl.isEmpty()) END
	
	
    }
    
}

    

