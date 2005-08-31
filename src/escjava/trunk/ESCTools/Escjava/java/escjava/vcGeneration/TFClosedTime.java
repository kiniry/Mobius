package escjava.vcGeneration;

// TBoolOp = return a boolean and sons are boolean : list(boolean) -> boolean
class TFClosedTime extends TFunction {

    public void typeTree(){
	
	if(sons.size()!=1)
	    System.err.println("TFclosedTime node with "+sons.size()+" instead of 1, that's strange...");
	else {
	    TNode n1 = getChildAt(0);

	    // we are sure about the type of the sons
	    n1.setType($Field,true);

	    n1.typeTree();
	}

    }

} 

// as trick : asElems asField asLockset
