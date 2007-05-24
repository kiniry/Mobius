package escjava.vcGeneration.coq;

import java.io.Writer;
import java.util.Iterator;

import escjava.vcGeneration.TAllocLE;
import escjava.vcGeneration.TAllocLT;
import escjava.vcGeneration.TAnyEQ;
import escjava.vcGeneration.TAnyNE;
import escjava.vcGeneration.TArrayFresh;
import escjava.vcGeneration.TArrayLength;
import escjava.vcGeneration.TArrayShapeMore;
import escjava.vcGeneration.TArrayShapeOne;
import escjava.vcGeneration.TAsElems;
import escjava.vcGeneration.TAsField;
import escjava.vcGeneration.TAsLockSet;
import escjava.vcGeneration.TBoolAnd;
import escjava.vcGeneration.TBoolEQ;
import escjava.vcGeneration.TBoolImplies;
import escjava.vcGeneration.TBoolNE;
import escjava.vcGeneration.TBoolNot;
import escjava.vcGeneration.TBoolOr;
import escjava.vcGeneration.TBoolean;
import escjava.vcGeneration.TCast;
import escjava.vcGeneration.TChar;
import escjava.vcGeneration.TDouble;
import escjava.vcGeneration.TEClosedTime;
import escjava.vcGeneration.TExist;
import escjava.vcGeneration.TFClosedTime;
import escjava.vcGeneration.TFloat;
import escjava.vcGeneration.TFloatAdd;
import escjava.vcGeneration.TFloatDiv;
import escjava.vcGeneration.TFloatEQ;
import escjava.vcGeneration.TFloatGE;
import escjava.vcGeneration.TFloatGT;
import escjava.vcGeneration.TFloatLE;
import escjava.vcGeneration.TFloatLT;
import escjava.vcGeneration.TFloatMod;
import escjava.vcGeneration.TFloatMul;
import escjava.vcGeneration.TFloatNE;
import escjava.vcGeneration.TForAll;
import escjava.vcGeneration.TFunction;
import escjava.vcGeneration.TInt;
import escjava.vcGeneration.TIntegralAdd;
import escjava.vcGeneration.TIntegralDiv;
import escjava.vcGeneration.TIntegralEQ;
import escjava.vcGeneration.TIntegralGE;
import escjava.vcGeneration.TIntegralGT;
import escjava.vcGeneration.TIntegralLE;
import escjava.vcGeneration.TIntegralLT;
import escjava.vcGeneration.TIntegralMod;
import escjava.vcGeneration.TIntegralMul;
import escjava.vcGeneration.TIntegralNE;
import escjava.vcGeneration.TIntegralSub;
import escjava.vcGeneration.TIs;
import escjava.vcGeneration.TIsAllocated;
import escjava.vcGeneration.TIsNewArray;
import escjava.vcGeneration.TLiteral;
import escjava.vcGeneration.TLockLE;
import escjava.vcGeneration.TLockLT;
import escjava.vcGeneration.TMethodCall;
import escjava.vcGeneration.TName;
import escjava.vcGeneration.TNode;
import escjava.vcGeneration.TNull;
import escjava.vcGeneration.TRefEQ;
import escjava.vcGeneration.TRefNE;
import escjava.vcGeneration.TRoot;
import escjava.vcGeneration.TSelect;
import escjava.vcGeneration.TStore;
import escjava.vcGeneration.TString;
import escjava.vcGeneration.TSum;
import escjava.vcGeneration.TTypeEQ;
import escjava.vcGeneration.TTypeLE;
import escjava.vcGeneration.TTypeNE;
import escjava.vcGeneration.TTypeOf;
import escjava.vcGeneration.TUnset;
import escjava.vcGeneration.coq.visitor.ABasicCoqVisitor;

public class SimpleVisitor extends ABasicCoqVisitor {

	protected SimpleVisitor(Writer out, CoqProver prover) {
		super(out, prover, null);
		this.tcbv = this;
		this.tcv = this;
	}
	
	//@ ensures vc == vc ++ [[s]] ++ 
    public void genericFun(/*@ non_null @*/ String s, TFunction n) {
    	out.appendI(s+" ");
    	//@ list args <- sons
    	int i =0;
    	
    	/*@ loop_invariant 
    	  @		\forall int i i in n.sons
    	  @ 			vc ++
    	  @*/
    	for(; i < n.sons.size(); i++) {
    		n.getChildAt(i).accept(tcv);
    		if(i != n.sons.size() - 1)
    			out.appendN(" ");
    	}


    	if((n.getChildAt(--i)) instanceof TName || (n.getChildAt(--i)) instanceof TLiteral)
    		out.reduceIwNl();
    	else
    		out.reduceI();    
    }
	//@ ensures vc == vc ++ (allocLE interp(arg1), interp(arg2))
	public void visitTAllocLE(TAllocLE n) {
		genericFun("allocLE", n);
	}

	public void visitTAllocLT(TAllocLT n) {
		genericFun("allocLT", n);		
	}

	public void visitTAnyEQ(TAnyEQ n) {
		genericFun("anyEQ", n);	
	}

	public void visitTAnyNE(TAnyNE n) {
		genericFun("anyNE", n);	
		
	}

	public void visitTArrayFresh(TArrayFresh n) {
		genericFun("arrayFresh", n);
		
	}

	public void visitTArrayLength(TArrayLength n) {
		genericFun("arrayLength", n);
	}

	public void visitTArrayShapeMore(TArrayShapeMore n) {
		genericFun("arrayShapeMore", n);
	}

	public void visitTArrayShapeOne(TArrayShapeOne n) {
		genericFun("arrayShapeOne", n);
	}

	public void visitTAsElems(TAsElems n) {
		genericFun("asElems", n);
		
	}

	public void visitTAsField(TAsField n)  {
		genericFun("asField", n);
	}

	public void visitTAsLockSet(TAsLockSet n) {
		genericFun("asLockSet", n);
	}

	public void visitTBoolAnd(TBoolAnd n) {
		genericFun("band", n);
	}

	public void visitTBoolEQ(TBoolEQ n) {
		genericFun("beq", n);
	}

	public void visitTBoolImplies(TBoolImplies n) {
		genericFun("bimplies", n);
	}

	public void visitTBoolNE(TBoolNE n) {
		genericFun("bne", n);
	}

	public void visitTBoolNot(TBoolNot n) {
		genericFun("bnot", n);
		
	}

	public void visitTBoolOr(TBoolOr n) {
		genericFun("bor", n);
	}

	public void visitTBoolean(TBoolean n) {
		out.appendN(""+ n.value);
	}

	public void visitTCast(TCast n) {
		genericFun("cast", n);
		
	}

	public void visitTChar(TChar n) {
		out.appendN(""+ n.value);
	}

	public void visitTDouble(TDouble n) {
		out.appendN(""+ n.value);
	}

	public void visitTEClosedTime(TEClosedTime n)  {
		genericFun("eClosedTime", n);
	}

	public void visitTExist(TExist n)  {
		genericFun("exist ", n);
	}

	public void visitTFClosedTime(TFClosedTime n)  {
		genericFun("fClosedTime", n);
	}

	public void visitTFloat(TFloat n)  {
		out.appendN(""+ n.value);		
	}

	public void visitTFloatAdd(TFloatAdd n)  {
		genericFun("fAdd", n);
		
	}

	public void visitTFloatDiv(TFloatDiv n) {
		genericFun("fDiv", n);
		
	}

	public void visitTFloatEQ(TFloatEQ n) {
		genericFun("fEQ", n);	
	}

	public void visitTFloatGE(TFloatGE n) {
		genericFun("fGE", n);
	}

	public void visitTFloatGT(TFloatGT n) {
		genericFun("fGT", n);
	}

	public void visitTFloatLE(TFloatLE n) {
		genericFun("fLE", n);
	}

	public void visitTFloatLT(TFloatLT n)  {
		genericFun("fLT", n);
	}

	public void visitTFloatMod(TFloatMod n)  {
		genericFun("fMod", n);
	}

	public void visitTFloatMul(TFloatMul n)  {
		genericFun("fMul", n);
	}

	public void visitTFloatNE(TFloatNE n)  {
		genericFun("fNE", n);
	}

	public void visitTForAll(TForAll n)  {
		genericFun("bforall", n);
	}

	public void visitTInt(TInt n)  {
		out.appendN(""+ n.value);
	}

	public void visitTIntegralAdd(TIntegralAdd n)  {
		genericFun("iAdd", n);
		
	}

	public void visitTIntegralDiv(TIntegralDiv n)  {
		genericFun("iDiv", n);
	}

	public void visitTIntegralEQ(TIntegralEQ n)  {
		genericFun("iEQ", n);
	}

	public void visitTIntegralGE(TIntegralGE n)  {
		genericFun("iGE", n);
	}

	public void visitTIntegralGT(TIntegralGT n)  {
		genericFun("iGT", n);
	}

	public void visitTIntegralLE(TIntegralLE n)  {
		genericFun("iLE", n);
	}

	public void visitTIntegralLT(TIntegralLT n)  {
		genericFun("iLT", n);
	}

	public void visitTIntegralMod(TIntegralMod n)  {
		genericFun("iMod", n);
	}

	public void visitTIntegralMul(TIntegralMul n)  {
		genericFun("iMul", n);
		
	}

	public void visitTIntegralNE(TIntegralNE n)  {
		genericFun("iNE", n);
		
	}

	public void visitTIntegralSub(TIntegralSub n)  {
		genericFun("iSub", n);
	}

	public void visitTIs(TIs n)  {
		genericFun("is", n);
	}

	public void visitTIsAllocated(TIsAllocated n)  {
		genericFun("bIsAllocated", n);
	}

	public void visitTIsNewArray(TIsNewArray n)  {
		genericFun("isNewArray", n);		
	}

	public void visitTLockLE(TLockLE n)  {
		genericFun("lockLE", n);
	}

	public void visitTLockLT(TLockLT n)  {
		genericFun("lockLT", n);
	}

	public void visitTMethodCall(TMethodCall call)  {
		genericFun(p.getVariableInfo(call.getName()), call);
	}

	public void visitTName(TName n)  {
		if(TNode._boolean.equals(n.type)){
			out.appendN("(bvar \"" + n.name + "\")");
		}
		else if(TNode._Path.equals(n.type)) {
			out.appendN("(pvar \"" + n.name + "\")");
		}
		else if(TNode._Reference.equals(n.type)) {
			out.appendN("(rvar \"" + n.name + "\")");
		}
		else if(TNode._Time.equals(n.type)) {
			out.appendN("(tmvar \"" + n.name + "\")");
		}
		else if(TNode._Type.equals(n.type)) {
			out.appendN("(tvar \"" + n.name + "\")");
		}
		else {
			out.appendN("(var \"" + n.name + "\")");
		}
	}

	public void visitTNull(TNull n)  {
		out.appendN("null");
	}

	public void visitTRefEQ(TRefEQ n)  {
		genericFun("refEQ", n);
		
	}

	public void visitTRefNE(TRefNE n)  {
		genericFun("refNE", n);
		
	}

	public void visitTRoot(TRoot n)  {
		Iterator iter = n.sons.iterator();
    	while(iter.hasNext()) {
    		((TNode)iter.next()).accept(tcv);
    	}
	}

	public void visitTTypeEQ(TTypeEQ n)  {
		genericFun("typeEQ", n);
		
	}

	public void visitTTypeLE(TTypeLE n)  {
		genericFun("typeLE", n);
		
	}

	public void visitTTypeNE(TTypeNE n)  {
		genericFun("typeNE", n);
		
	}

	public void visitTTypeOf(TTypeOf n)  {
		genericFun("typeof", n);	
	}
	
	public void visitTSum(TSum n) {
		genericFun("sum", n);
	}
	
	public void visitTUnset(TUnset n)  {
		genericFun("unset", n);	
	}

	public void visitTString(TString n)  {
		out.appendN("\""+ n.value +"\"");
	}
	

    public void visitTSelect(/*@ non_null @*/ TSelect n) {
    	String pre = "";
    	if(TNode._integer.equals(((TNode)n.sons.get(1)).type))
    		pre = "arr";
    	genericFun("Heap." +pre +"select ", n);
    }
    
    
    public void visitTStore(/*@ non_null @*/ TStore n) {
    	String pre = "";
    	TNode index =(TNode)n.sons.get(1);
    	if(TNode._integer.equals(index.type))
    		pre = "arr";
    	genericFun("Heap." + pre + "store ", n);
    }

}
