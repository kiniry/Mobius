package escjava.vcGeneration.coq;

import escjava.vcGeneration.TBoolean;
import escjava.vcGeneration.TName;
import escjava.vcGeneration.TNode;
import escjava.vcGeneration.VariableInfo;



public class TCoqBoolVisitor extends TCoqVisitor {
	TCoqBoolVisitor(TCoqVisitor v, CoqStringBuffer o, CoqProver p){
    	super(v, o, p);	
    }
	 public void visitTBoolean(/*@ non_null @*/ TBoolean n){	
		if(n.value)
		    out.appendN("true");
		else
		    out.appendN("false");
	 }
	 
	 public void visitTName(/*@ non_null @*/ TName n){

			/*
			 * This call handles everything, ie if n is a variable or a type name
			 */
		    	VariableInfo vi = TNode.getVariableInfo(n.name);
		    	String name = p.getVariableInfo(vi);
		    	if(name.equals("Z"))
		    		name = "T_Z";
				out.appendN(name + " = true");
	 }
}
