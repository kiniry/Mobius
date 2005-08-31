package escjava.vcGeneration;

// TBoolOp = return a boolean and sons are boolean : list(boolean) -> boolean
class TAnyEQ extends TFunction {

    public void typeTree(){
	
	/*
	 * Semantic control
	 */

	if(sons.size() < 2)
	    System.err.println("AnyEQ node has a different number of sons = "+sons.size()+" which is < from 2, bizarre...");
	else
	    // retrieve the son and compare their type
	    {
		TNode n1 = getChildAt(0);
		TNode n2 = getChildAt(1);
		TypeInfo vi1 = n1.type;
		TypeInfo vi2 = n2.type;
		

		if(vi1 == null || vi2 == null)
		    System.err.println("Not able to infer type in an AnyEQ node");
		else {
		    if(vi1 == null && vi2 != null)
			n1.type = vi2;
		    else if(vi1 != null && vi2 == null)
			n2.type = vi1;
		}

		n1.typeTree();
		n2.typeTree();
	    }

    }

}

