package escjava.vcGeneration.coq.visitor;

import java.io.*;

import escjava.vcGeneration.*;
import escjava.vcGeneration.coq.CoqProver;
import escjava.vcGeneration.PrettyPrinter;

public abstract class AFloatVisitor extends AIntegralVisitor {

	protected AFloatVisitor(Writer out, CoqProver prover, PrettyPrinter ppout) {
		super(out, prover, ppout);
	}
	
	public void visitTFloat(/*@ non_null @*/ TFloat n) throws IOException{
		out.appendN(" (* a float value *)"+n.value);
	}
    public void visitTFloatEQ(/*@ non_null @*/ TFloatEQ n) throws IOException{
    	spacedBinOp("(* Float Eq *) =", n);
    }
				  
    public void visitTFloatGE(/*@ non_null @*/ TFloatGE n) throws IOException{
    	binOp(">=", n); 
    }
				  
    public void visitTFloatGT(/*@ non_null @*/ TFloatGT n) throws IOException{
    	binOp(">", n); 
    }
				  
    public void visitTFloatLE(/*@ non_null @*/ TFloatLE n) throws IOException{
    	binOp("<=", n); 
    }
				  
    public void visitTFloatLT(/*@ non_null @*/ TFloatLT n) throws IOException{
    	binOp("<", n); 
    }
				  
    public void visitTFloatNE(/*@ non_null @*/ TFloatNE n) throws IOException{
    	binOp("<>", n); 
    }
    
				  
    public void visitTFloatAdd(/*@ non_null @*/ TFloatAdd n) throws IOException{
    	binOp("+", n); 
    }

    public void visitTFloatDiv(/*@ non_null @*/ TFloatDiv n) throws IOException{
    	binOp("/", n); 
    }

    public void visitTFloatMod(/*@ non_null @*/ TFloatMod n) throws IOException{
    	binOp("mod", n);
    }

    public void visitTFloatMul(/*@ non_null @*/ TFloatMul n) throws IOException{
    	binOp("*", n);
    }
}
