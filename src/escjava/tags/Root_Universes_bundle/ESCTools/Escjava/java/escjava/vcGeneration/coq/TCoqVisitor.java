package escjava.vcGeneration.coq;

import java.io.*;

import escjava.vcGeneration.*;
import escjava.vcGeneration.coq.visitor.ANotHandledVisitor;

/**
 * In the Coq extension, we differentiate <code>Boolean</code>
 * value and variables from usual <code>Prop</code>.
 * So we have 2 visitors which are coupled. 
 * <p>
 * This is the visitor used for <code>Boolean</code> 
 * used as <code>Prop</code> values. This class, the main Coq visitor
 * is divided into smaller parts handling the different domain-specific
 * functions. For instance all the functions on the Int are in the
 * visitor class {@link escjava.vcGeneration.coq.visitor.AIntegralVisitor}.
 * @see escjava.vcGeneration.coq.visitor
 * @author J.Charles based on the work of C.Hurlin
 * @version 14/11/2005
 */
class TCoqVisitor extends ANotHandledVisitor {

    
	TCoqVisitor(Writer out, CoqProver prover){
		super(out, prover, null);
		setVisitors(this, new TCoqBoolVisitor(out, this, super.out, p));
    }
    
    protected TCoqVisitor(Writer out, TCoqVisitor v, PrettyPrinter ppout, CoqProver p){
    	super(out, p, ppout);
    	setVisitors(v, this);
    }


    /* 
     * non automatic generated class
     */ 
    public void visitTName(/*@ non_null @*/ TName n) throws IOException{

	/*
	 * This call handles everything, ie if n is a variable or a type name
	 */
    	VariableInfo vi = TNode.getVariableInfo(n.name);
    	String name = p.getVariableInfo(vi);
    	if(name.equals("Z"))
    		name = "T_Z";
		out.appendN(name);
    }

    public void visitTRoot(/*@ non_null @*/ TRoot n) throws IOException{
	
	for(int i = 0; i <= n.sons.size() - 1; i++)
	    n.getChildAt(i).accept(tcv);

    }

    /*
     * class created using the perl script
     */
    public void visitTBoolImplies(/*@ non_null @*/ TBoolImplies n) throws IOException{
    	genericPropOp("->", n);
    }

    public void visitTBoolAnd(/*@ non_null @*/ TBoolAnd n) throws IOException{
    	genericPropOp("/\\", n);
    }

    public void visitTBoolOr(/*@ non_null @*/ TBoolOr n) throws IOException{
    	genericPropOp("\\/", n);
    }

    public void visitTBoolNot(/*@ non_null @*/ TBoolNot n) throws IOException{
    	unaryGeneric("negb ", n);
    }
    
    public void visitTBoolEQ(/*@ non_null @*/ TBoolEQ n) throws IOException{
    
    	printBoolEq(n);
    
    }
    public void printBoolEq(TFunction n) throws IOException{
    	//String s = "=";
       	if(n.sons.size() < 2 )
    	    System.err.println("java.escjava.vcGeneration.TCoqVisitor.printBoolEq : the spaced out binary operator named = has a number of sons equals to "+n.sons.size()+" which is different from 2");
    	out.appendI("(");
    	for(int i =0; i < n.sons.size() - 1; i++) {
    		
    		if(i != 0) {
    			out.appendN(" /\\ (");
    		}
    		else
    			out.appendN("(");
    		Object o = (n.getChildAt(i+1));
    		if((o instanceof TBoolean)) {
    			n.getChildAt(i).accept(tcv);
    			out.appendN(" = ");	
    			n.getChildAt(i+1).accept(tcv);
    		}
    		else {
    			n.getChildAt(i).accept(tcbv);
    			out.appendN(" <-> ");
    			n.getChildAt(i+1).accept(tcbv);
    		}

			
    		out.appendN(")");
    	}
    	out.appendN(")");
    	if((n.getChildAt(1)) instanceof TName || (n.getChildAt(1)) instanceof TLiteral)
    	    out.reduceIwNl();
    	else
    	    out.reduceI();
    }
    
    public void visitTBoolNE(/*@ non_null @*/ TBoolNE n) throws IOException{
    	binOp("<>", n);
    }

    public void visitTAllocLT(/*@ non_null @*/ TAllocLT n) throws IOException{
    	binOp("<", n);
    }

    public void visitTAllocLE(/*@ non_null @*/ TAllocLE n) throws IOException{
    	binOp("<=", n);
    }

    public void visitTAnyEQ(/*@ non_null @*/ TAnyEQ n) throws IOException{
    	if(n.sons.size() == 2) {
    		Object son = n.sons.get(1);
    		if((son instanceof TAsLockSet) || 
    				(son instanceof TAsElems) ||
    				(son instanceof TAsField)) {
    			out.appendN("(* TAs *) True ");
    			return;
    		}
    	}
    	
    	spacedBinOp("(* Any Eq *) =", n);
    	
    }

    public void visitTAnyNE(/*@ non_null @*/ TAnyNE n) throws IOException{
    	binOp("<>", n);
    }
    
		

				  
    public void visitTRefEQ(/*@ non_null @*/ TRefEQ n) throws IOException{
    	spacedBinOp("(* Ref Eq *) =", n);
    }
				  
    public void visitTRefNE(/*@ non_null @*/ TRefNE n) throws IOException{
    	binOp("<>", n);
    }
				  
    public void visitTTypeEQ(/*@ non_null @*/ TTypeEQ n) throws IOException{
    	spacedBinOp("(* Type Eq *) =", n);
    }
				  
    public void visitTTypeNE(/*@ non_null @*/ TTypeNE n) throws IOException{
    	binOp("<>", n);
    }
				  
    public void visitTTypeLE(/*@ non_null @*/ TTypeLE n) throws IOException{
    	genericFun("subtypes", n); //
    }
	
 


    public void visitTTypeOf(/*@ non_null @*/ TTypeOf n) throws IOException{
    	genericFun("typeof",n);
    }

    public void visitTForAll(/*@ non_null @*/ TForAll n) throws IOException{
    	out.appendI("(forall ");	
    	int i =0;
    	StringBuffer sb = new StringBuffer();
    	//n.generateDeclarations(sb);
    	out.appendN(sb.toString());
    	for(; i < n.sons.size(); i++) {
    	    TNode a = n.getChildAt(i);
    	    
    	    /*
    	     * If not last, output a space
    	     */
    	    if(!(a instanceof TName)) {
    	    	break;
    	    }
    	    
    	    out.appendN( "(");
    	    TName var = (TName) a;
    	    tcv.visitTName(var);
    	    
    	    out.appendN(  ": "+ p.getTypeInfo(TNode.getVariableInfo(var.name).type) + ")");
    	    
    	}
    	out.appendN(","); 
    	if( i <n.sons.size() - 1)
    		i++;
    	
    	TNode a = n.getChildAt(i);
    	out.appendN(" ");    
    	a.accept(tcv);
    	out.appendN(")");
    	out.reduceI();
    }

    //
				  
    public void visitTIsAllocated(/*@ non_null @*/ TIsAllocated n) throws IOException{
    	genericFun("isAllocated", n);
    }

    public void visitTEClosedTime(/*@ non_null @*/ TEClosedTime n) throws IOException{
    	genericFun("eClosedTime", n);
    }
				  
    public void visitTFClosedTime(/*@ non_null @*/ TFClosedTime n) throws IOException{
    	genericFun("fClosedTime", n);
    }
    public void visitTAsElems(/*@ non_null @*/ TAsElems n) throws IOException{
    	genericFun("asElems", n);
    }
				  
    public void visitTAsField(/*@ non_null @*/ TAsField n) throws IOException{
    	genericFun("asField", n);
    }

    public void visitTString(/*@ non_null @*/ TString n) throws IOException{
    	out.appendN(" (typeof " + n.value+ ")" );
    }

    public void visitTBoolean(/*@ non_null @*/ TBoolean n) throws IOException{
	if(n.value)
	    out.appendN(" (* bool*) true");
	else
	    out.appendN("false");
    }

    public void visitTChar(/*@ non_null @*/ TChar n) throws IOException{
	out.appendN(" (* a char value *)"+n.value);
    }
	  
    public void visitTDouble(/*@ non_null @*/ TDouble n) throws IOException{
    	out.appendN(" (* a double value *)"+n.value); 
    }
    public void visitTNull(/*@ non_null @*/ TNull n) throws IOException{
    	out.appendN(" null");
    }

	public void visitTMethodCall(/*@non_null*/TMethodCall call) throws IOException {
		genericFun(p.getVariableInfo(call.getName()), call);
	}

	public void visitTUnset(/*@non_null*/TUnset n) throws IOException {
		genericFun("unset", n);
	}

	public void visitTSum(TSum s) {
		// TODO Auto-generated method stub
		
	}


}
