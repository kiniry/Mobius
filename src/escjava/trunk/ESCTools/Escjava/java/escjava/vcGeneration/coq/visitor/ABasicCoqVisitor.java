package escjava.vcGeneration.coq.visitor;

import escjava.vcGeneration.*;
import escjava.vcGeneration.coq.CoqProver;
import escjava.vcGeneration.coq.CoqStringBuffer;

public abstract class ABasicCoqVisitor extends TVisitor{
	protected ABasicCoqVisitor tcbv;
    protected ABasicCoqVisitor tcv;
    
    /**
     * The output buffer.
     */
    protected CoqStringBuffer out = null;
    /**
     * The current instance of the CoqProver.
     */
    protected CoqProver p;
    
    
    
    protected ABasicCoqVisitor(CoqProver prover, CoqStringBuffer out) {
    	if(out == null)
    		this.out = new CoqStringBuffer(super.out);
    	else
    		this.out = out;
    	
    	p= prover;	
    }
    
    protected void setVisitors(ABasicCoqVisitor tcv, ABasicCoqVisitor tcbv) {
    	this.tcv = tcv;
    	this.tcbv = tcbv;
    }
    /*
     * General Function
     * You give the operator at the first argument and then it outputs
     * op (son1, son2 ...)
     * )
     */
    public void genericFun(/*@ non_null @*/ String s, TFunction n){

	out.appendI("("+ s+" ");
	
	int i =0;
	for(; i < n.sons.size(); i++) {
		
	    n.getChildAt(i).accept(this);

	    /*
	     * If not last, output a space
	     */
	    if(i != n.sons.size() - 1)
		out.appendN(" ");
	}
	out.appendN(")");

	if((n.getChildAt(--i)) instanceof TName || (n.getChildAt(--i)) instanceof TLiteral)
	    out.reduceIwNl();
	else
	    out.reduceI();
	    
    }
    public void propFun(/*@ non_null @*/ String s, TFunction n){

    	out.appendI("("+ s+" ");
    	
    	int i =0;
    	for(; i < n.sons.size(); i++) {
    		
    	    n.getChildAt(i).accept(tcbv);

    	    /*
    	     * If not last, output a space
    	     */
    	    if(i != n.sons.size() - 1)
    		out.appendN(" ");
    	}
    	out.appendN(")");

    	if((n.getChildAt(--i)) instanceof TName || (n.getChildAt(--i)) instanceof TLiteral)
    	    out.reduceIwNl();
    	else
    	    out.reduceI();
    	    
        }
    /*
     * Function/Operator with arity 1 :
     * (op X)
     */
    public void unaryGeneric(/*@ non_null @*/ String s, TFunction n){

	if(n.sons.size() != 1)
	    System.err.println("java.escjava.vcGeneration.TCoqVisitor.unFun : an unary operator named "+s+" has a number of sons equals to "+n.sons.size()+" which is different from 1");
	out.appendI("(");
	out.appendN(s);
	out.appendN(" (");
	n.getChildAt(0).accept(this);
	out.appendN("))");
	if((n.getChildAt(0)) instanceof TName || (n.getChildAt(0)) instanceof TLiteral)
	    out.reduceIwNl();
	else
	    out.reduceI();
	    
    }

    /*
     * You give the operator at the first argument and then it outputs
     *   (son1 
        op 
	  son2 ... 
	op 
	  sonN)
     */
    public void genericOp(/*@ non_null @*/ String s, TFunction n){

	out.appendI("(");

	int i =0;
//	for(int j = 0; j < n.sons.size(); j++)
//		out.appendN("(");
	for(; i < n.sons.size(); i++) {
		out.appendN("(");
	    n.getChildAt(i).accept(this);
	    //if(i != 0)
		out.appendN(")");
	    /*
	     * not the last
	     */
	    if(i != n.sons.size() - 1) {
	    	out.appendN("\n");
	    	out.append(s);
	    }
	    
	    out.appendN(" ");
	}
	//for(int j = 0; j <= i; j++)
		out.appendN(")");
	out.reduceI();
    }
    public void genericPropOp(/*@ non_null @*/ String s, TFunction n){

    	out.appendI("(");

    	int i =0;
//    	for(int j = 0; j < n.sons.size(); j++)
//    		out.appendN("(");
    	for(; i < n.sons.size(); i++) {
    		out.appendN("(");
    	    n.getChildAt(i).accept(this);
    	    if(n.getChildAt(i) instanceof TName)
    	    	out.appendN(" = true");
    	    //if(i != 0)
    		out.appendN(")");
    	    /*
    	     * not the last
    	     */
    	    if(i != n.sons.size() - 1) {
    	    	out.appendN("\n");
    	    	out.append(s);
    	    }
    	    
    	    out.appendN(" ");
    	}
    	//for(int j = 0; j <= i; j++)
    		out.appendN(")");
    	out.reduceI();
        }
    /*
     * Function/Operator with arity 1 :
     * (op X)
     */
    public void unaryProp(/*@ non_null @*/ String s, TFunction n){

	if(n.sons.size() != 1)
	    System.err.println("java.escjava.vcGeneration.TCoqVisitor.unFun : an unary operator named "+s+" has a number of sons equals to "+n.sons.size()+" which is different from 1");
	out.appendI("(");
	out.appendN(s);
	out.appendN(" (");
	n.getChildAt(0).accept(tcv);
	 if(n.getChildAt(0) instanceof TName)
	    	out.appendN(" = true");
	out.appendN("))");
	if((n.getChildAt(0)) instanceof TName || (n.getChildAt(0)) instanceof TLiteral)
	    out.reduceIwNl();
	else
	    out.reduceI();
	    
    }
    /*
     * Function for binary operator
     * You give the operator at the first argument and then it outputs
     * (son1 
     * op 
     * son2)
     * 
     * If son1 is a variable, op isn't on the next line
     * If son2 is a variable, it doesn't go to next line.
     */
    public void binOp(/*@ non_null @*/ String s, TFunction n){

	if(n.sons.size() != 2)
	    System.err.println("java.escjava.vcGeneration.TCoqVisitor : a binary operator named "+s+" has a number of sons equals to "+n.sons.size()+" which is different from 2");

	out.appendI("(");
	
	n.getChildAt(0).accept(tcv);

	if(! ((n.getChildAt(0)) instanceof TName || (n.getChildAt(0)) instanceof TLiteral)) {
	    out.appendN("\n");
	    out.append("");
	}
	
	out.appendN(" "+s+" ");
	n.getChildAt(1).accept(tcv);
	out.appendN(")");
	if((n.getChildAt(1)) instanceof TName || (n.getChildAt(1)) instanceof TLiteral)
	    out.reduceIwNl();
	else
	    out.reduceI();
	    
    }
    public void spacedBinOp(/*@ non_null @*/ String s, TFunction n){

    	if(n.sons.size() < 2 )
    	    System.err.println("java.escjava.vcGeneration.TCoqVisitor : the spaced out binary operator named "+s+" has a number of sons equals to "+n.sons.size()+" which is different from 2");

    	out.appendI("(");
    	for(int i =0; i < n.sons.size() - 1; i++) {
    		
    		if(i != 0) {
    			out.appendN(" /\\ (");
    		}
    		else
    			out.appendN("(");
    		// Frankie says... no equality on Prop
    		n.getChildAt(i).accept(tcv);    	
    		out.appendN(" "+s+" ");
    		n.getChildAt(i+1).accept(tcv);
    		out.appendN(")");
    	}
    	out.appendN(")");
    	if((n.getChildAt(1)) instanceof TName || (n.getChildAt(1)) instanceof TLiteral)
    	    out.reduceIwNl();
    	else
    	    out.reduceI();
    	    
        }
}
