package escjava.vcGeneration;

// TBoolOp = return a boolean and sons are boolean : list(boolean) -> boolean
class TIs extends TBoolRes { // %Reference | double | char etc ..., type -> boolean

    public void typeTree(){
	
	if(sons.size()!=2)
	    System.err.println("TIs node with "+sons.size()+" instead of 2, that's strange...");
	else {
	    TNode n1 = getChildAt(0);
	    TNode n2 = getChildAt(1);

	    /*
	     * As the son #1 can be a reference of have a final type,
	     * we can't guess it here. We just know that the second son should
	     * be a type.
	     */
	    n2.setType($Type,true);

	    n1.typeTree();
	    n2.typeTree();
	}

    }

} 

// %Field * %Reference -> %Reference | double | char etc... (final types)
