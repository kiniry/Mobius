package escjava.vcGeneration;

// TBoolOp = return a boolean and sons are boolean : list(boolean) -> boolean
class TBoolImplies extends TBoolOp {

    public void accept(TVisitor v){
	v.visitTBoolImplies(this);
    }
    
}

class TBoolAnd extends TBoolOp {
    
    public void accept(/*@ non_null @*/ TVisitor v){
	v.visitTBoolAnd(this);
    }

}

class TBoolOr extends TBoolOp {

    public void accept(/*@ non_null @*/ TVisitor v){
	v.visitTBoolOr(this);
    }

}

class TBoolNot extends TBoolOp {

    public void accept(/*@ non_null @*/ TVisitor v){
	v.visitTBoolNot(this);
    }

}

class TBoolEQ extends TBoolOp {

    public void accept(/*@ non_null @*/ TVisitor v){
	v.visitTBoolEQ(this);
    }

}

class TBoolNE extends TBoolOp {

    public void accept(/*@ non_null @*/ TVisitor v){
	v.visitTBoolNE(this);
    }

}

// allocation comparisons
// $Time * $Time -> boolean
class TAllocLT extends TBoolRes {

    public void typeTree(){
	
	/*
	 * Semantic control
	 */

	if(sons.size() < 2)
	    TDisplay.err(this, "typeTree()", "Node has a different number of sons = "+sons.size()+" which is < from 2, bizarre...");
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

    public void accept(/*@ non_null @*/ TVisitor v){
	v.visitTAllocLT(this);
    }

}

// $Time * $Time -> boolean
class TAllocLE extends TBoolRes {

    public void typeTree(){
	
	/*
	 * Semantic control
	 */

	if(sons.size() < 2)
	    TDisplay.err(this, "typeTree()", "Node has a different number of sons = "+sons.size()+" which is < from 2, bizarre...");
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

    public void accept(/*@ non_null @*/ TVisitor v){
	v.visitTAllocLE(this);
    }

}



// fixme
class TAnyEQ extends TFunction {

    public void typeTree(){
	
	/*
	 * Semantic control
	 */

	if(sons.size() < 2)
	    TDisplay.err(this, "typeTree()", "Node has a different number of sons = "+sons.size()+" which is < from 2, bizarre...");
	else
	    // retrieve the son and compare their type
	    {
		TNode n1 = getChildAt(0);
		TNode n2 = getChildAt(1);
		TypeInfo vi1 = n1.getTypeInfo();
		TypeInfo vi2 = n2.getTypeInfo();
		

		if(vi1 == null & vi2 == null)
		    TDisplay.warn(this, "typeTree()", "Not able to infer type in an AnyEQ node");
		else {
		    if(vi1 == null & vi2 != null) {
			TDisplay.info(this, "typeTree()", "Inferring that node "+n1.toString()+ " has type "+vi2.old+" because it's a son of an AnyEQ node which other son has type "+vi2.old);
			
			n1.setType(vi2, true);
		    }
		    else if(vi1 != null & vi2 == null) {
			TDisplay.info(this, "typeTree()", "Inferring that node "+n2.toString()+ " has type "+vi1.old+" because it's a son of an AnyEQ node which other son has type "+vi1.old);
			n2.setType(vi1, true);
		    }
		}

		n1.typeTree();
		n2.typeTree();
	    }

    }

    public void accept(/*@ non_null @*/ TVisitor v){
	v.visitTAnyEQ(this);
    }

}

class TAnyNE extends TFunction {

    public void accept(/*@ non_null @*/ TVisitor v){
	v.visitTAnyNE(this);
    }

}

// integral comparisons, TIntOp : int * int -> boolean
class TIntegralEQ extends TIntOp {

    public void accept(/*@ non_null @*/ TVisitor v){
	v.visitTIntegralEQ(this);
    }

}

class TIntegralGE extends TIntOp {

    public void accept(/*@ non_null @*/ TVisitor v){
	v.visitTIntegralGE(this);
    }

}

class TIntegralGT extends TIntOp {

    public void accept(/*@ non_null @*/ TVisitor v){
	v.visitTIntegralGT(this);
    }

}

class TIntegralLE extends TIntOp {

    public void accept(/*@ non_null @*/ TVisitor v){
	v.visitTIntegralLE(this);
    }

}

class TIntegralLT extends TIntOp {

    public void accept(/*@ non_null @*/ TVisitor v){
	v.visitTIntegralLT(this);
    }

}

class TIntegralNE extends TIntOp {

    public void accept(/*@ non_null @*/ TVisitor v){
	v.visitTIntegralNE(this);
    }

}

// integral operation : TIntFun : int * int -> int
class TIntegralAdd extends TIntFun {

    public void accept(/*@ non_null @*/ TVisitor v){
	v.visitTIntegralAdd(this);
    }

}

class TIntegralDiv extends TIntFun {

    public void accept(/*@ non_null @*/ TVisitor v){
	v.visitTIntegralDiv(this);
    }

}

class TIntegralMod extends TIntFun {

    public void accept(/*@ non_null @*/ TVisitor v){
	v.visitTIntegralMod(this);
    }

}

class TIntegralMul extends TIntFun {

    public void accept(/*@ non_null @*/ TVisitor v){
	v.visitTIntegralMul(this);
    }

}

//real comparisons : TFloatOp : float * float -> boolean
class TFloatEQ extends TFloatOp {

    public void accept(/*@ non_null @*/ TVisitor v){
	v.visitTFloatEQ(this);
    }

}

class TFloatGE extends TFloatOp {

    public void accept(/*@ non_null @*/ TVisitor v){
	v.visitTFloatGE(this);
    }

}

class TFloatGT extends TFloatOp {

    public void accept(/*@ non_null @*/ TVisitor v){
	v.visitTFloatGT(this);
    }

}

class TFloatLE extends TFloatOp {

    public void accept(/*@ non_null @*/ TVisitor v){
	v.visitTFloatLE(this);
    }

}

class TFloatLT extends TFloatOp {

    public void accept(/*@ non_null @*/ TVisitor v){
	v.visitTFloatLT(this);
    }

}

class TFloatNE extends TFloatOp {

    public void accept(/*@ non_null @*/ TVisitor v){
	v.visitTFloatNE(this);
    }

}

// float operation : TFloatFun : float * float -> float
class TFloatAdd extends TFloatFun {

    public void accept(/*@ non_null @*/ TVisitor v){
	v.visitTFloatAdd(this);
    }

}

class TFloatDiv extends TFloatFun {

    public void accept(/*@ non_null @*/ TVisitor v){
	v.visitTFloatDiv(this);
    }

}

class TFloatMod extends TFloatFun {

    public void accept(/*@ non_null @*/ TVisitor v){
	v.visitTFloatMod(this);
    }

}

class TFloatMul extends TFloatFun {

    public void accept(/*@ non_null @*/ TVisitor v){
	v.visitTFloatMul(this);
    }

}

// lock comparisons
class TLockLE extends TFunction {

    public void accept(/*@ non_null @*/ TVisitor v){
	v.visitTLockLE(this);
    }

}

class TLockLT extends TFunction {

    public void accept(/*@ non_null @*/ TVisitor v){
	v.visitTLockLT(this);
    }

}

// reference comparisons : %Reference * %Reference -> boolean
class TRefEQ extends TRefOp {

    public void accept(/*@ non_null @*/ TVisitor v){
	v.visitTRefEQ(this);
    }

}

class TRefNE extends TRefOp {

    public void accept(/*@ non_null @*/ TVisitor v){
	v.visitTRefNE(this);
    }

}

// type comparisons : %Type * %Type -> boolean
class TTypeEQ extends TTypeOp {

    public void accept(/*@ non_null @*/ TVisitor v){
	v.visitTTypeEQ(this);
    }

}

class TTypeNE extends TTypeOp {

    public void accept(/*@ non_null @*/ TVisitor v){
	v.visitTTypeNE(this);
    }

}

class TTypeLE extends TTypeOp {

    public void accept(/*@ non_null @*/ TVisitor v){
	v.visitTTypeLE(this);
    }

}

// usual functions, cast is select store typeof 

class TCast extends TBoolRes{

    public void typeTree(){}
    
    public void accept(/*@ non_null @*/ TVisitor v){
	v.visitTCast(this);
    }

}

class TIs extends TBoolRes { // %Reference | double | char etc ..., type -> boolean

    public void typeTree(){
	
	if(sons.size()!=2)
	    TDisplay.err(this, "typeTree()", "Node with "+sons.size()+" instead of 2, that's strange...");
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

    public void accept(/*@ non_null @*/ TVisitor v){
	v.visitTIs(this);
    }

} 

// %Field * %Reference -> %Reference | double | char etc... (final types)
class TSelect extends TFunction {

    public void typeTree(){
	
	if(sons.size()!=2)
	    TDisplay.err(this, "typeTree()", "Node with "+sons.size()+" instead of 2, that's strange...");
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

    public void accept(/*@ non_null @*/ TVisitor v){
	v.visitTSelect(this);
    }

}

// fixme
// %Field * %Reference * ? (value, %Reference?) -> memory
class TStore extends TFunction {

    public void typeTree(){
	
	if(sons.size()!=3)
	    TDisplay.err(this, "typeTree()", "TStore node with "+sons.size()+" instead of 3, that's strange...");
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

    public void accept(/*@ non_null @*/ TVisitor v){
	v.visitTStore(this);
    }

} 

// %Reference -> %Type
class TTypeOf extends TFunction {
    
    public TTypeOf(){
	type = $Type;
    }

    public void accept(/*@ non_null @*/ TVisitor v){
	v.visitTTypeOf(this);
    }

}

//quantifier
// bool -> bool // fixme
class TForAll extends TBoolRes {

    public void accept(/*@ non_null @*/ TVisitor v){
	v.visitTForAll(this);
    }

} 

// bool -> bool // fixme
class TExist extends TBoolRes {

    public void accept(/*@ non_null @*/ TVisitor v){
	v.visitTExist(this);
    }

} 

// allocation
class TIsAllocated extends TBoolOp {

    public void typeTree(){
	
	if(sons.size()!=2)
	    TDisplay.err(this, "typeTree()", "Node with "+sons.size()+" instead of 2, that's strange...");
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

    public void accept(/*@ non_null @*/ TVisitor v){
	v.visitTIsAllocated(this);
    }

} // %Reference -> bool

// %Reference -> %Time
class TEClosedTime extends TFunction {

    protected TEClosedTime(){
	type = $Time;
    }

    public void accept(/*@ non_null @*/ TVisitor v){
	v.visitTEClosedTime(this);
    }

} 

// %ReferenceField -> %Time
class TFClosedTime extends TFunction {

    protected TFClosedTime(){
	type = $Time;
    }

    public void typeTree(){
	
	if(sons.size()!=1)
	    TDisplay.err(this, "typeTree()", "Node with "+sons.size()+" instead of 1, that's strange...");
	else {
	    TNode n1 = getChildAt(0);

	    // we are sure about the type of the sons
	    n1.setType($Field,true);

	    n1.typeTree();
	}

    }

    public void accept(/*@ non_null @*/ TVisitor v){
	v.visitTFClosedTime(this);
    }

} 

// as trick : asElems asField asLockset
class TAsElems extends TFunction {

    public void accept(/*@ non_null @*/ TVisitor v){
	v.visitTAsElems(this);
    }

}

class TAsField extends TFunction {

    public void typeTree(){
	
	if(sons.size()!=2)
	    TDisplay.err(this, "typeTree()", "Node with "+sons.size()+" instead of 2, that's strange...");
	else {
	    TNode n1 = getChildAt(0);
	    TNode n2 = getChildAt(1);

	    /* we are sure about the type of the sons
	     * The types of the second son is set first, thus
	     * we can use it for the first one.
	     */
	    n2.setType($Type,true);
	    n2.typeTree();
	    
	    // we say this is a field
	    n1.setType($Field,true);
	    // we add his own type too
	    VariableInfo vi = n1.getVariableInfo();

	    vi.setSecondType(n2.getTypeInfo());

 	    n1.typeTree();
	}

    }

    public void accept(/*@ non_null @*/ TVisitor v){
	v.visitTAsField(this);
    }

}

class TAsLockSet extends TFunction {

    public void accept(/*@ non_null @*/ TVisitor v){
	v.visitTAsLockSet(this);
    }

}

//array 
// %ArrayReference -> integer
class TArrayLength extends TFunction {

    public void accept(/*@ non_null @*/ TVisitor v){
	v.visitTArrayLength(this);
    }

}

//
class TArrayFresh extends TFunction {

    public void accept(/*@ non_null @*/ TVisitor v){
	v.visitTArrayFresh(this);
    }

} 

class TArrayShapeOne extends TFunction {

    public void accept(/*@ non_null @*/ TVisitor v){
	v.visitTArrayShapeOne(this);
    }

}

class TArrayShapeMore extends TFunction {

    public void accept(/*@ non_null @*/ TVisitor v){
	v.visitTArrayShapeMore(this);
    }

}

class TIsNewArray extends TFunction {

    public void accept(/*@ non_null @*/ TVisitor v){
	v.visitTIsNewArray(this);
    }

}
