package escjava.vcGeneration.coq.visitor;

import escjava.vcGeneration.*;
import escjava.vcGeneration.coq.CoqProver;
import escjava.vcGeneration.coq.CoqStringBuffer;
public abstract class AIntegralVisitor extends ABasicCoqVisitor {
	
	protected AIntegralVisitor(CoqProver p, CoqStringBuffer out) {
		super(p, out);
	}
    
	public void visitTIntegralEQ(/*@ non_null @*/ TIntegralEQ n){
    	binOp(" =", n);
    }
    
    public void visitTIntegralGE(/*@ non_null @*/ TIntegralGE n){
    	binOp(">=", n);
    }
    
    public void visitTIntegralGT(/*@ non_null @*/ TIntegralGT n){
    	binOp(">", n);
    }

    public void visitTIntegralLE(/*@ non_null @*/ TIntegralLE n){
    	binOp("<=", n);
    }
    
    public void visitTIntegralLT(/*@ non_null @*/ TIntegralLT n){
    	binOp("<", n);
    }
    
    public void visitTIntegralNE(/*@ non_null @*/ TIntegralNE n){
    	binOp("<>", n);
    }
    
    public void visitTIntegralAdd(/*@ non_null @*/ TIntegralAdd n){
    	binOp("+", n);
    }
    
    public void visitTIntegralDiv(/*@ non_null @*/ TIntegralDiv n){
    	binOp("/", n); 
    }

    public void visitTIntegralMod(/*@ non_null @*/ TIntegralMod n) {
    	binOp("mod", n); 
    }

    public void visitTIntegralMul(/*@ non_null @*/ TIntegralMul n){
    	binOp("*", n);
    }

	public void visitTIntegralSub(TIntegralSub n) {
		binOp("-", n);
	}
    public void visitTInt(/*@ non_null @*/ TInt n){
    	out.appendN(n.value + ""); 
    }
}
