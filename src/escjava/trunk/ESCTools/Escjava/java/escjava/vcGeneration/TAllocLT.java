package escjava.vcGeneration;

// TBoolOp = return a boolean and sons are boolean : list(boolean) -> boolean
class TAllocLT extends TBoolRes {

    public void typeTree(){
	
	/*
	 * Semantic control
	 */

	if(sons.size() < 2)
	    System.err.println("AllocLT node has a different number of sons = "+sons.size()+" which is < from 2, bizarre...");
	else {
	    TNode n1 = getChildAt(0);
	    TNode n2 = getChildAt(1);

	    // we are sure about the type of the sons
	    n1.setType($Time,true);
	    n2.setType($Time,true);

	    n1.typeTree();
	    n2.typeTree();
	}

    }

}

// $Time * $Time -> boolean
