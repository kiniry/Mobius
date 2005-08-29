package escjava.vcGeneration;

// TBoolOp = return a boolean and sons are boolean : list(boolean) -> boolean
class TBoolImplies extends TBoolOp {}

class TBoolAnd extends TBoolOp {}

class TBoolOr extends TBoolOp {}

class TBoolNot extends TBoolOp {}

class TBoolEQ extends TBoolOp {}

class TBoolNE extends TBoolOp {}

// allocation comparisons
class TAllocLT extends TBoolOp {}

class TAllocLE extends TBoolOp {}

// fixme
class TAnyEQ extends TFunction {

    public void typeTree(){
	
	/*
	 * Semantic control
	 */

	if(sons.size() != 2)
	    System.err.println("AnyEQ node has a different number of sons = "+sons.size()+" which is != from 2, bizarre...");
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
class TIs extends TFunction {} // %Reference, type -> integer

class TSelect extends TFunction {} // memory * %Reference -> object

class TStore extends TFunction {} // memory * %Reference * index -> memory

// %Reference -> %Type
class TTypeOf extends TFunction {
    
    public TTypeOf(){
	type = $Type;
    }

}

//quantifier
class TForAll extends TFunction {} // bool -> bool // fixme

class TExist extends TFunction {} // bool -> bool // fixme

// allocation
class TIsAllocated extends TBoolOp {} // %Reference -> bool

class TEClosedTime extends TFunction {} // %Reference -> integer

class TFClosedTime extends TFunction {} // %Reference -> integer

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

