package checkingIF;



/**
 * Created on Jan 25, 2005
 * @version $Id: CheckingVisitor.java,v 1.4 2005/03/21 09:36:37 lmartini Exp $
 */

/**
 * @author Luca Martini
 * 
 *  
 */
import embeddingInfo.AbstractSecLevelMethod;
import embeddingInfo.SecLevel;
import exc.GeneralCheckingError;
import exc.SecSpecificationError;
import exc.TypeCheckError;
import org.apache.bcel.generic.AALOAD;
import org.apache.bcel.generic.AASTORE;
import org.apache.bcel.generic.ACONST_NULL;
import org.apache.bcel.generic.ARETURN;
import org.apache.bcel.generic.ARRAYLENGTH;
import org.apache.bcel.generic.ASTORE;
import org.apache.bcel.generic.ArrayInstruction;
import org.apache.bcel.generic.ArrayType;
import org.apache.bcel.generic.BALOAD;
import org.apache.bcel.generic.BASTORE;
import org.apache.bcel.generic.CALOAD;
import org.apache.bcel.generic.CASTORE;
import org.apache.bcel.generic.ConstantPoolGen;
import org.apache.bcel.generic.ConstantPushInstruction;
import org.apache.bcel.generic.ConversionInstruction;
import org.apache.bcel.generic.DUP2;
import org.apache.bcel.generic.DUP2_X1;
import org.apache.bcel.generic.DUP2_X2;
import org.apache.bcel.generic.DUP;
import org.apache.bcel.generic.DUP_X1;
import org.apache.bcel.generic.EmptyVisitor;
import org.apache.bcel.generic.FADD;
import org.apache.bcel.generic.FALOAD;
import org.apache.bcel.generic.FASTORE;
import org.apache.bcel.generic.FCMPG;
import org.apache.bcel.generic.FCMPL;
import org.apache.bcel.generic.FDIV;
import org.apache.bcel.generic.FMUL;
import org.apache.bcel.generic.FNEG;
import org.apache.bcel.generic.FREM;
import org.apache.bcel.generic.FSUB;
import org.apache.bcel.generic.GETFIELD;
import org.apache.bcel.generic.GETSTATIC;
import org.apache.bcel.generic.IADD;
import org.apache.bcel.generic.IALOAD;
import org.apache.bcel.generic.IAND;
import org.apache.bcel.generic.IASTORE;
import org.apache.bcel.generic.IDIV;
import org.apache.bcel.generic.IINC;
import org.apache.bcel.generic.IMUL;
import org.apache.bcel.generic.INEG;
import org.apache.bcel.generic.INVOKESTATIC;
import org.apache.bcel.generic.IOR;
import org.apache.bcel.generic.IREM;
import org.apache.bcel.generic.ISHL;
import org.apache.bcel.generic.ISHR;
import org.apache.bcel.generic.ISUB;
import org.apache.bcel.generic.IUSHR;
import org.apache.bcel.generic.IXOR;
import org.apache.bcel.generic.IfInstruction;
import org.apache.bcel.generic.Instruction;
import org.apache.bcel.generic.InstructionHandle;
import org.apache.bcel.generic.InvokeInstruction;
import org.apache.bcel.generic.LDC;
import org.apache.bcel.generic.LDC_W;
import org.apache.bcel.generic.LoadInstruction;
import org.apache.bcel.generic.MethodGen;
import org.apache.bcel.generic.NEW;
import org.apache.bcel.generic.NEWARRAY;
import org.apache.bcel.generic.POP2;
import org.apache.bcel.generic.POP;
import org.apache.bcel.generic.PUTFIELD;
import org.apache.bcel.generic.PUTSTATIC;
import org.apache.bcel.generic.RETURN;
import org.apache.bcel.generic.ReturnInstruction;
import org.apache.bcel.generic.SALOAD;
import org.apache.bcel.generic.SASTORE;
import org.apache.bcel.generic.SWAP;
import org.apache.bcel.generic.StackConsumer;
import org.apache.bcel.generic.StoreInstruction;
import org.apache.bcel.generic.Type;

public class CheckingVisitor extends EmptyVisitor {

    /**
     * The executionstate we're operating on.
     */
    private State state;

    /**
     * The InstructionHandle currently being checked
     *
     */
    private InstructionHandle ih;

    /**
     * The method we're checking. (needed to handle Ret)
     */
    private MethodGen method;
    
    /**
     * The ConstantPool we're using.
     */
    private ConstantPoolGen cpg;
    
    /**
     * This is the level of <code>this</code> in the current check
     *
     */
    private SecLevel impl;
    
    /**
     * This is the level of the program counter in the current check
     * (must be set!!!!!!)
     */
    private SecLevel pcLevel;

    /**
     * A reference to the used control flow graph. Needed to obtain
     * region information.
     *
     */
    private ControlFlowGraph cfg;

    /**
     * Constructor. Constructs a new instance of this class.
     */
    public CheckingVisitor(MethodGen method, ConstantPoolGen cpg, SecLevel impl, ControlFlowGraph cfg){
	this.method = method;
	this.cpg = cpg;
	this.impl = impl; 
	this.cfg = cfg;
    }

    public void setState(State s, InstructionHandle ih) {
	state = s;
	this.ih = ih;
	pcLevel = s.getSe().get(ih);
    }
    
    /**
     * The OperandStack from the current State we're operating on.
     * @see #setState(State)
     */
    private OpStack stack(){
	return state.getStack();
    }
    
    /**
     * The Security Environment from the current State we're operating on.
     * @see #setState(State)
     */
    private SecEnv se(){
	return state.getSe();
    }
 
    /** Symbolically executes the corresponding Java Virtual Machine
     * instruction. Please note that a null reference can be seen also
     * like an array reference.*/ 
    public void visitACONST_NULL(ACONST_NULL o){
	SecLevel s=(SecLevel) pcLevel.clone();
	s.isArray=true;
	s.levelArray = s.level;
	stack().push(s);
    }
    
    /**
     * All load instructrion:
     * Except: DLOAD, LLOAD
     */
    public void visitLoadInstruction(LoadInstruction o){
	stack().push
	    (getSLRegister(o.getIndex()).
	     lub(pcLevel));
    } 
    
    /**
     * All return instructrion:
     * Except: DRETURN, RETURN
     */
    public void visitReturnInstruction(ReturnInstruction o){
	if (!(o instanceof RETURN)) { 
	    SecLevel k = stack().peek();
	    SecLevel k2 = GetInfo.signature(method.getMethod(), impl).return_value;
	    // k <= k2 
	    if (!(k.leq(k2))) {
		constraintViolated(o,"Returned value ("+k+") higher than signature specification ("+k2+").");
	    }
	    
	    if ((o instanceof ARETURN) &&
		(method.getReturnType() instanceof ArrayType)) {
		if (!k.isArray) 
		    constraintViolated(o,"Trying to return a non-array reference when the method must return an array reference");
		if (!(k.levelArray == k2.level))
		    constraintViolated(o,"Returned values is an array reference lower than signature specification");
	    }
	    // only executed if no exception is thrown before
	    stack().pop();
	}
    }	
    
    public void visitStoreInstruction(StoreInstruction o){		
	SecLevel k=stack().peek();
	SecLevel reg=getSLRegister(o.getIndex());
	// se(i) sup k <= vt(x)
	if (!(k.lub(pcLevel).
	      leq(reg)))
	    constraintViolated(o,"Stored Level violates method security assignement for registers. k= "+k+", se =" +pcLevel+", vt(x) = "+reg+".");
	// checking array assignment
	if ((o instanceof ASTORE) && (reg.isArray)){
	    if (!k.isArray) // this is a type-safety check (not necessary)
		constraintViolated(o,"Storing a non-array reference into an array-declared register");
	    if ((!k.equalsArray(reg))) {
		constraintViolated(o,"Storing a low array reference to a high array reference.\nStored reference = "+k+", register = "+reg);
	    }
	}
	// only executed if no exception is thrown before
	stack().pop();
	
    }
    /** Symbolically executes the corresponding Java Virtual Machine instruction. */ 
    public void visitDUP(DUP o){
	SecLevel s1 = stack().pop();
	stack().push(s1);
	stack().push(s1);
    }

    /** Symbolically executes the corresponding Java Virtual Machine
     * instruction. Only the first form.
     */ 
    public void visitDUP_X1(DUP_X1 o){
	SecLevel w1 = stack().pop();
	SecLevel w2 = stack().pop();
	stack().push(w1);
	stack().push(w2);
	stack().push(w1);
    }
    
    
    /** Symbolically executes the corresponding Java Virtual Machine
     * instruction. */ 
    public void visitDUP2(DUP2 o){
	SecLevel t = stack().pop();
	SecLevel u = stack().pop();
	stack().push(u);
	stack().push(t);
	stack().push(u);
	stack().push(t);
    }
    
    /** Symbolically executes the corresponding Java Virtual Machine
     * instruction. */ 
    public void visitDUP2_X1(DUP2_X1 o){
	SecLevel t = stack().pop();
	SecLevel u = stack().pop();
	SecLevel v = stack().pop();
	stack().push(u);
	stack().push(t);
	stack().push(v);
	stack().push(u);
	stack().push(t);
    }
    
    
    /** Symbolically executes the corresponding Java Virtual Machine
     * instruction. */ 
    public void visitDUP2_X2(DUP2_X2 o){
	SecLevel t = stack().pop();   
	SecLevel u = stack().pop();
	SecLevel v = stack().pop();
	SecLevel w = stack().pop();
	stack().push(u);
	stack().push(t);
	stack().push(w);
	stack().push(v);
	stack().push(u);
	stack().push(t);
    }
    
    public void visitFADD(FADD o){
	primOp(o);
    }
    
    public void visitFCMPG(FCMPG o){
	primOp(o);
    }

    public void visitFCMPL(FCMPL o){
	primOp(o);
    }
    
    /**
     * Handles BIPUSH, DCONST, FCONST, ICONST, LCONST, SIPUSH
     */
    public void visitConstantPushInstruction(ConstantPushInstruction o) {
	stack().push(pcLevel);
    }

    public void visitFDIV(FDIV o){
	primOp(o);
    }
    
    public void visitFMUL(FMUL o){
	primOp(o);
    }
    
    public void visitFNEG(FNEG o){
	liftTop(o);
    }
    

    public void visitFREM(FREM o){
	primOp(o);
    }
    
    public void visitFSUB(FSUB o){
	primOp(o);
    }
    
    public void visitGETFIELD(GETFIELD o){
	SecLevel k = stack().pop();
	SecLevel fieldLevel=GetInfo.level(o,cpg);
        k.sup(fieldLevel);
	k.sup(pcLevel);
	if (o.getFieldType(cpg) instanceof ArrayType) {
	    // if the field is an array reference, then set the proper
	    // value for the levelArray
	    k.isArray = true;
	    k.levelArray = fieldLevel.level; 
	}
	stack().push(k);
	// lifting of the s.e. (due to exceptions)
	se().lift(k,cfg.region(ih));
    }

    public void visitGETSTATIC(GETSTATIC o){
	stack().push(pcLevel);
    }
    
    /**
     * Only works for instrunctions that do not manipulate Double or Long
     Handles:  F2I, I2B, I2C, I2F, I2S, 
    */
    public void visitConversionInstruction(ConversionInstruction o){
	liftTop(o);
    }
    
    public void visitIADD(IADD o){
	primOp(o);
    }
    
    public void visitIAND(IAND o){
	primOp(o);
    }
    
    public void visitIDIV(IDIV o) {
	primOp(o);
    }
    
    public void visitIfInstruction(IfInstruction o) {
	SecLevel k = stack().pop();
	if (o.consumeStack(cpg) == 2) 
	    k.sup(stack().pop());
	stack().lift(k);
	se().lift(k,cfg.region(ih));
    }
    
    public void visitIINC(IINC o) {
	// no changes to stack and se 
	// but a check is needed
	SecLevel reg=getSLRegister(o.getIndex());
	if (!(reg.lub(pcLevel).leq(reg))) {
	    constraintViolated(o,"Incrementing a local variable with level "+reg+" when the security enviroment is "+pcLevel);
	}
    }

    public void visitIMUL(IMUL o) {
	primOp(o);
    }
    
    public void visitINEG(INEG o) { 
	liftTop(o);
    }
    
    public void visitInvokeInstruction(InvokeInstruction o) {
	Type[] parametersType = o.getArgumentTypes(cpg);
	int nargs = parametersType.length;
	AbstractSecLevelMethod slm;
	if (!(o instanceof INVOKESTATIC)) {
	    SecLevel call_impl = stack().peek(nargs);
	    try {
		slm = GetInfo.signature(o,cpg,call_impl);
	    } catch (SecSpecificationError e) {
		System.err.println(e.getMessage()+ "\nExiting...");
		System.exit(0);
		return;
	    }
	
	    if ((!call_impl.leq(pcLevel) || 
		 (!pcLevel.leq(slm.effect)))) {
		constraintViolated(o,"Constraint k1<=se(i)<=k3 violated");
	    }
	    // check parameters consistency
	    for (int j = nargs; j > 0; j--) {
		// parameters are pushed in the reverse order
		SecLevel param = stack().pop();
		if (!param.leq(slm.registers[j])) {
		    constraintViolated(o,"Parameter number "+j+" called with a security level "+param+" not less than or equal to the level "+slm.registers[j]+ "specified by the signature (Implicit value="+call_impl+").");
		}
		
		if (parametersType[j-1] instanceof ArrayType) {
		    if (!param.isArray) 
			constraintViolated(o,"Parameter number "+j+" must be an array reference");
		    if (param.levelArray != slm.registers[j].level) {
			constraintViolated(o,"Parameter number "+j+" is an array reference and its imutable level "+param+" does not agree with the method signature"+ slm.registers[j]+".");
		    }
		}
    	    }
	    // popping the object reference
	    stack().pop();
	    if (o.getReturnType(cpg) != Type.VOID)
		stack().push(slm.return_value);
	    SecLevel k1k4 = call_impl.lub(slm.exceffect);
	    stack().lift(k1k4);
	    se().lift(k1k4,cfg.region(ih));
	}
	
    }
    
    public void visitIOR(IOR o) {
	primOp(o);
    }
    
    public void visitIREM(IREM o) {
	primOp(o);
    }
    
    public void visitISHL(ISHL o) {
	primOp(o);
    }

    public void visitISHR(ISHR o) {
	primOp(o);
    }
    
    public void visitISUB(ISUB o) {
	primOp(o);
    }

    public void visitIUSHR(IUSHR o) {
	primOp(o);
    }

    public void visitIXOR(IXOR o) {
	primOp(o);
    }

    public void visitLDC(LDC o){
	liftTop(o);
    }
    
    public void visitLDC_W(LDC_W o){
	liftTop(o);
    }
    
    public void visitNEW(NEW o){
	stack().push(pcLevel);
    }

    public void visitPOP(POP o){
	stack().pop();
    }
    
    public void visitPOP2(POP2 o){
	stack().pop();
	stack().pop();
    }

    public void visitPUTFIELD(PUTFIELD o){
	SecLevel k1 = stack().peek();
	SecLevel k2 = stack().peek(1);
	SecLevel levelField = GetInfo.level(o,cpg);
	
	if (!(k1.
	      lub(k2).
	      lub(pcLevel).
	      leq(levelField))) 
	    constraintViolated(o, "Seclevel k1 U k2 U se(i) = (" +k1 +
			       " U " + k2 + " U " + pcLevel + ") = " + 
			       k1.lub(k2).lub(pcLevel) + 
			       " is not less or equal to ft(f) = " +
			       levelField);	
	
	// to exclude flows l->h in arrays
	if (o.getFieldType(cpg) instanceof ArrayType) {
	    if (!k2.isArray) 
		constraintViolated(o,"Trying to store into an array field a value that is not an array reference");
	    
	    if (k2.levelArray != levelField.level)
		constraintViolated(o,"Assigning an array reference of security level "+ k2 +" to a an array field of security level "+GetInfo.level(o,cpg)+".");
	}
	
	if (!GetInfo.signature(method.getMethod(),impl).effect.leq(pcLevel)) {
	    constraintViolated(o,"Modifying the heap with a level"+GetInfo.signature(method.getMethod(),impl).effect+" when the level of the environment is "+pcLevel+".");   
	}
	
	stack().pop();
	stack().pop();
	// lifting of the s.e. (due to exceptions)
	se().lift(k1,cfg.region(ih));
    }
    
    public void visitPUTSTATIC(PUTSTATIC o){
	SecLevel k1 = stack().peek();
	// to exclude flows l->h in arrays
	if ((o.getFieldType(cpg) instanceof ArrayType) &&
	    (!k1.equals(GetInfo.level(o,cpg)))){
	    constraintViolated(o,"Assigning an array reference of security level "+k1+" to a an array field of security level "+GetInfo.level(o,cpg)+".");
	}
	if (!(k1.
	      lub(pcLevel).
	      leq(GetInfo.level(o,cpg)))) 
	    constraintViolated(o, "Seclevel k1  U se(i) = " +k1 +
			       " U " + pcLevel + " = " + 
			       k1.lub(pcLevel) + 
			       "is not less or equal to ft(f) = " +
			       GetInfo.level(o,cpg));
    }
    
    public void visitSWAP(SWAP o){
	SecLevel s1 = stack().pop();
	SecLevel s2 = stack().pop();
	stack().push(s1);
	stack().push(s2);
    }

    /***********************************
     *
     *    START Array instructions
     *
     **********************************/

    public void visitAALOAD(AALOAD o) {
	visitXALOAD(o);
    }

    public void visitBALOAD(BALOAD o) {
	visitXALOAD(o);
    }

    public void visitCALOAD(CALOAD o) {
	visitXALOAD(o);
    }

    public void visitFALOAD(FALOAD o) {
	visitXALOAD(o);
    }
    
    public void visitIALOAD(IALOAD o) {
	visitXALOAD(o);
    }
    
    public void visitSALOAD(SALOAD o) {
	visitXALOAD(o);
    }
    
    public void visitAASTORE(AASTORE o) {
	visitXASTORE(o);
    }
    
    public void visitBASTORE(BASTORE o) {
	visitXASTORE(o);
    }

    public void visitCASTORE(CASTORE o) {
	visitXASTORE(o);
    }
    
    public void visitFASTORE(FASTORE o) {
	visitXASTORE(o);
    }
    
    public void visitIASTORE(IASTORE o) {
	visitXASTORE(o);
    }
    
    public void visitSASTORE(SASTORE o) {
	visitXASTORE(o);
    }

    public void visitNEWARRAY(NEWARRAY o) {
	liftTop(o);
	SecLevel createdArray=stack().peek();
	createdArray.isArray = true;
	createdArray.levelArray = createdArray.level;
    }

    public void visitARRAYLENGTH(ARRAYLENGTH o) {
	SecLevel ref = stack().peek();
	if (!ref.isArray) {
	    constraintViolated(o,"The reference that is used for this arraylength instruction is not an array reference.");
	}

	SecLevel tmp = liftTop(o);
	se().lift(tmp,cfg.region(ih));
    }

    public void visitXALOAD(ArrayInstruction o) {
	SecLevel ref = stack().peek(1);
	if (!ref.isArray) {
	    constraintViolated(o,"The reference that is used for this array load instruction is not an array reference.");
	}
	SecLevel k = primOp(o);
	se().lift(k,cfg.region(ih));
    }
    
    public void visitXASTORE(ArrayInstruction o) {
	SecLevel value = stack().pop();
	SecLevel index = stack().pop();
	SecLevel ref = stack().pop();
	if (!(ref.isArray)) {
	    constraintViolated(o,"Constraint violated: array typing error, trying to use "+ref+" in place of an array reference.");
	}
	
	if (!(value.lub(pcLevel).lub(index).leqA(ref)))
	    constraintViolated(o,"Constraint violated: se(i) U val U index = " +pcLevel+ " U "+value+ "= "+ pcLevel + " U " +index+" is not less or equal to array(ref) = "+ref+".");
	// 	if (!(value.lub(pcLevel).leq(index)))
	// 	    constraintViolated(o,"Constraint violated: se(i) U val = " +pcLevel+ " U "+value+ "= "+ value.lub(pcLevel)+ " is not less or equal to index = "+index+".");
    }
    
    /***********************************
     *
     *   END Array instructions
     *
     **********************************/
    
    private final SecLevel primOp(Instruction o){
	SecLevel ret = stack().pop().
	    lub(stack().pop()).
	    lub(pcLevel);
	stack().push(ret);
	return ret;
    }

    private final SecLevel liftTop(Instruction o) {
	SecLevel t = stack().pop();
	stack().push
	    (t.sup(pcLevel));
	return t;
    }
    

    /**
     *  <code>isArray</code> tells if the register whose number is
     *  passed as parameter holds an array value.
     */
    private boolean isArray(int i) {
	try {
	    return GetInfo.signature(method.getMethod(), impl).isArray(i);
	} catch (SecSpecificationError e) {
	    System.err.println(e.getMessage()+ "\nExiting...");
	    System.exit(0);
	    return true;
	}
    }
    
    /**
     * Retrieves the security level of the register passed as
     * parameter
     */
    private SecLevel getSLRegister(int i) {
	try {
	    return GetInfo.signature(method.getMethod(), impl).registers[i];
	} catch (SecSpecificationError e) {
	    System.err.println(e.getMessage()+ "\nExiting...");
	    System.exit(0);
	    return null;
	}
    }
    
    private void constraintViolated(Instruction i, String descr) {
	//throw new GeneralCheckingError("Type checking error during verification of instruction "+i+"\n"+descr);
	throw new TypeCheckError("Type checking error during verification of instruction "+ i +"\n"+descr);
    }
}
