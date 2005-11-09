package escjava.vcGeneration.coq;

import escjava.vcGeneration.TBoolean;



public class TCoqBoolVisitor extends TCoqVisitor {
	TCoqBoolVisitor(CoqStringBuffer o, CoqProver p){
    	super(o, p);	
    }
	 public void visitTBoolean(/*@ non_null @*/ TBoolean n){	
		if(n.value)
		    out.appendN("true");
		else
		    out.appendN("false");
	 }
}
