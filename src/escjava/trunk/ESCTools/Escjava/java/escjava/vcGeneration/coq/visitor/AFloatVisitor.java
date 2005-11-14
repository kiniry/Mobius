package escjava.vcGeneration.coq.visitor;

import escjava.vcGeneration.*;
import escjava.vcGeneration.coq.CoqProver;
import escjava.vcGeneration.coq.CoqStringBuffer;
public abstract class AFloatVisitor extends AIntegralVisitor {

	protected AFloatVisitor(CoqProver prover, CoqStringBuffer out) {
		super(prover, out);
	}
	
	public void visitTFloat(/*@ non_null @*/ TFloat n){
		out.appendN(" (* a float value *)"+n.value);
	}
    public void visitTFloatEQ(/*@ non_null @*/ TFloatEQ n){
    	spacedBinOp("(* Float Eq *) =", n);
    }
				  
    public void visitTFloatGE(/*@ non_null @*/ TFloatGE n){
    	binOp(">=", n); 
    }
				  
    public void visitTFloatGT(/*@ non_null @*/ TFloatGT n){
    	binOp(">", n); 
    }
				  
    public void visitTFloatLE(/*@ non_null @*/ TFloatLE n){
    	binOp("<=", n); 
    }
				  
    public void visitTFloatLT(/*@ non_null @*/ TFloatLT n){
    	binOp("<", n); 
    }
				  
    public void visitTFloatNE(/*@ non_null @*/ TFloatNE n){
    	binOp("<>", n); 
    }
    
				  
    public void visitTFloatAdd(/*@ non_null @*/ TFloatAdd n){
    	binOp("+", n); 
    }

    public void visitTFloatDiv(/*@ non_null @*/ TFloatDiv n){
    	binOp("/", n); 
    }

    public void visitTFloatMod(/*@ non_null @*/ TFloatMod n){
    	binOp("mod", n);
    }

    public void visitTFloatMul(/*@ non_null @*/ TFloatMul n){
    	binOp("*", n);
    }
}
