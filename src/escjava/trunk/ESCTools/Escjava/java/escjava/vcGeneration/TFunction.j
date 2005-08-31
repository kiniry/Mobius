package escjava.vcGeneration;

// TBoolOp = return a boolean and sons are boolean : list(boolean) -> boolean
class TBoolImplies extends TBoolOp {}

class TBoolAnd extends TBoolOp {}

class TBoolOr extends TBoolOp {}

class TBoolNot extends TBoolOp {}

class TBoolEQ extends TBoolOp {}

class TBoolNE extends TBoolOp {}

// allocation comparisons
// $Time * $Time -> boolean
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
class TAllocLE extends TBoolRes {

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



// fixme
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

class TAnyNE extends TFunction {}

// integral comparisons, TIntOp : int * int -> boolean
class TIntegralEQ extends TIntOp {}

class TIntegralGE extends TIntOp {}

class TIntegralGT extends TIntOp {}

class TIntegralLE extends TIntOp {}

class TIntegralLT extends TIntOp {}

class TIntegralNE extends TIntOp {}

// integral operation : TIntFun : int * int -> int
class TIntegralAdd extends TIntFun {}

class TIntegralDiv extends TIntFun {}

class TIntegralMod extends TIntFun {}

class TIntegralMul extends TIntFun {}

//real comparisons : TFloatOp : float * float -> boolean
class TFloatEQ extends TFloatOp {}

class TFloatGE extends TFloatOp {}

class TFloatGT extends TFloatOp {}

class TFloatLE extends TFloatOp {}

class TFloatLT extends TFloatOp {}

class TFloatNE extends TFloatOp {}

// float operation : TFloatFun : float * float -> float
class TFloatAdd extends TFloatFun {}

class TFloatDiv extends TFloatFun {}

class TFloatMod extends TFloatFun {}

class TFloatMul extends TFloatFun {}

// lock comparisons
class TLockLE extends TFunction {}

class TLockLT extends TFunction {}

// reference comparisons : %Reference * %Reference -> boolean
class TRefEQ extends TRefOp {}

class TRefNE extends TRefOp {}

// type comparisons : %Type * %Type -> boolean
class TTypeEQ extends TTypeOp {}

class TTypeNE extends TTypeOp {}

class TTypeLE extends TTypeOp {}

// usual functions, is select store typeof isAllocated
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
class TSelect extends TFunction {

        public void typeTree(){
	
	if(sons.size()!=2)
	    System.err.println("TSelect node with "+sons.size()+" instead of 2, that's strange...");
	else {
	    TNode n1 = getChildAt(0);
	    TNode n2 = getChildAt(1);

	    /*
	     * As the son #1 can be a reference of have a final type,
	     * we can't guess it here. We just know that the second son should
	     * be a %Reference.
	     */
	    n2.setType($Reference,true);

	    n1.typeTree();
	    n2.typeTree();
	}

    }

}

// fixme
// %Field * %Reference * ? (value, %Reference?) -> memory
class TStore extends TFunction {

        public void typeTree(){
	
	if(sons.size()!=3)
	    System.err.println("TStore node with "+sons.size()+" instead of 3, that's strange...");
	else {
	    TNode n1 = getChildAt(0);
	    TNode n2 = getChildAt(1);
	    TNode n3 = getChildAt(2);

	    n1.setType($Field, true);
	    n2.setType($Reference,true);

	    n1.typeTree();
	    n2.typeTree();
	    n3.typeTree();
	}

    }

} 

// %Reference -> %Type
class TTypeOf extends TFunction {
    
    public TTypeOf(){
	type = $Type;
    }

}

//quantifier
class TForAll extends TBoolRes {} // bool -> bool // fixme

class TExist extends TBoolRes {} // bool -> bool // fixme

// allocation
class TIsAllocated extends TBoolOp {

    public void typeTree(){
	
	if(sons.size()!=2)
	    System.err.println("TIsAllocated node with "+sons.size()+" instead of 2, that's strange...");
	else {
	    TNode n1 = getChildAt(0);
	    TNode n2 = getChildAt(1);

	    // we are sure about the type of the sons
	    n1.setType($Reference,true);
	    n2.setType($Time,true);

	    n1.typeTree();
	    n2.typeTree();
	}

    }

} // %Reference -> bool

class TEClosedTime extends TFunction {} // %Reference -> integer

// %ReferenceField -> %Time
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
class TAsElems extends TFunction {}

class TAsField extends TFunction {}

class TAsLockSet extends TFunction {}

//array 
class TArrayLength extends TFunction {} // %Reference -> integer

class TArrayFresh extends TFunction {} //

class TArrayShapeOne extends TFunction {}

class TArrayShapeMore extends TFunction {}

class TIsNewArray extends TFunction {}

