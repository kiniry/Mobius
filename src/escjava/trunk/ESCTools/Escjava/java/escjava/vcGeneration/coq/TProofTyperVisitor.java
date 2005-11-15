package escjava.vcGeneration.coq;

import escjava.vcGeneration.*;
/**
 * Coq extension needs 'clear' typing.
 * This retyping is done using the known function signatures.
 * This is done without any subtleties.
 * @author J. Charles
 * @version last update: 15/11/2005
 */
public class TProofTyperVisitor extends TVisitor {

	public void setAllTypesTo(TFunction f, TypeInfo ti) {
		for(int i = 0; i < f.sons.size(); i++) {
			TNode t = f.getChildAt(i);
			t.type = ti;
			t.accept(this);
		}
	}
	public void visitSons(TFunction f) {
		for(int i = 0; i < f.sons.size(); i++) {
			TNode t = f.getChildAt(i);
			t.accept(this);
		}
	}
	public boolean sonsAreBool(TFunction f) {
		for(int i = 0; i < f.sons.size(); i++) {
			TNode t = f.getChildAt(i);
			if(TNode.$boolean.equals(t.type))
				return true;
		}
		return false;
	}
	
	public void visitTName(TName n) {
	}

	public void visitTRoot(TRoot n) {
		visitSons(n);
	}

	public void visitTBoolImplies(TBoolImplies n) {
		n.type = TNode.$boolean;
		setAllTypesTo(n, TNode.$boolean);
	}

	public void visitTBoolAnd(TBoolAnd n) {
		n.type = TNode.$boolean;
		setAllTypesTo(n, TNode.$boolean);
	}

	public void visitTBoolOr(TBoolOr n) {
		n.type = TNode.$boolean;
		setAllTypesTo(n, TNode.$boolean);
	}

	public void visitTBoolNot(TBoolNot n) {
		n.type = TNode.$boolean;
		setAllTypesTo(n, TNode.$boolean);
	}

	public void visitTBoolEQ(TBoolEQ n) {
		n.type = TNode.$boolean;
		setAllTypesTo(n, TNode.$boolean);
	}

	public void visitTBoolNE(TBoolNE n) {
		n.type = TNode.$boolean;
		setAllTypesTo(n, TNode.$boolean);
	}

	public void visitTAllocLT(TAllocLT n) {
		visitSons(n);
		// TODO Auto-generated method stub
		
	}

	public void visitTAllocLE(TAllocLE n) {
		visitSons(n);
		// TODO Auto-generated method stub
		
	}

	public void visitTAnyEQ(TAnyEQ n) {
		visitSons(n);
		if(sonsAreBool(n)) {
			// in fact the node was wrong.
			TFunction parent = n.parent;
			int ind = parent.sons.indexOf(n);
			TBoolEQ beq = new TBoolEQ();
			for(int i = 0; i < n.sons.size(); i++) {
				TNode t = n.getChildAt(i);
				beq.sons.add(t);
			}
			parent.sons.setElementAt(beq, ind);
			beq.accept(this);
		} else {
			n.type = TNode.$boolean;
		}
		
	}

	public void visitTAnyNE(TAnyNE n) {
		visitSons(n);
		n.type = TNode.$boolean;
		// TODO Auto-generated method stub
		
	}

	public void visitTIntegralEQ(TIntegralEQ n) {
		n.type = TNode.$boolean;
		setAllTypesTo(n, TNode.$integer);
	}

	public void visitTIntegralGE(TIntegralGE n) {
		n.type = TNode.$boolean;
		setAllTypesTo(n, TNode.$integer);
	}

	public void visitTIntegralGT(TIntegralGT n) {
		n.type = TNode.$boolean;
		setAllTypesTo(n, TNode.$integer);
	}

	public void visitTIntegralLE(TIntegralLE n) {
		n.type = TNode.$boolean;
		setAllTypesTo(n, TNode.$integer);
		
	}

	public void visitTIntegralLT(TIntegralLT n) {
		n.type = TNode.$boolean;
		setAllTypesTo(n, TNode.$integer);
		
	}

	public void visitTIntegralNE(TIntegralNE n) {
		n.type = TNode.$boolean;
		setAllTypesTo(n, TNode.$integer);
	}

	public void visitTIntegralAdd(TIntegralAdd n) {
		n.type = TNode.$integer;
		setAllTypesTo(n, TNode.$integer);
	}

	public void visitTIntegralDiv(TIntegralDiv n) {
		n.type = TNode.$integer;
		setAllTypesTo(n, TNode.$integer);
		
	}

	public void visitTIntegralMod(TIntegralMod n) {
		n.type = TNode.$integer;
		setAllTypesTo(n, TNode.$integer);
	}

	public void visitTIntegralMul(TIntegralMul n) {
		n.type = TNode.$integer;
		setAllTypesTo(n, TNode.$integer);	
	}
	
	public void visitTIntegralSub(TIntegralSub n) {
		n.type = TNode.$integer;
		setAllTypesTo(n, TNode.$integer);
	}

	public void visitTFloatEQ(TFloatEQ n) {
		n.type = TNode.$boolean;
		visitSons(n);
		// TODO Auto-generated method stub
		
	}

	public void visitTFloatGE(TFloatGE n) {
		n.type = TNode.$boolean;
		visitSons(n);
		// TODO Auto-generated method stub
		
	}

	public void visitTFloatGT(TFloatGT n) {
		n.type = TNode.$boolean;
		visitSons(n);
		// TODO Auto-generated method stub
		
	}

	public void visitTFloatLE(TFloatLE n) {
		n.type = TNode.$boolean;
		visitSons(n);
		// TODO Auto-generated method stub
		
	}

	public void visitTFloatLT(TFloatLT n) {
		n.type = TNode.$boolean;
		visitSons(n);
		// TODO Auto-generated method stub
		
	}

	public void visitTFloatNE(TFloatNE n) {
		n.type = TNode.$boolean;
		visitSons(n);
		// TODO Auto-generated method stub
		
	}

	public void visitTFloatAdd(TFloatAdd n) {
		visitSons(n);
		// TODO Auto-generated method stub
		
	}

	public void visitTFloatDiv(TFloatDiv n) {
		visitSons(n);
		// TODO Auto-generated method stub
		
	}

	public void visitTFloatMod(TFloatMod n) {
		visitSons(n);
		// TODO Auto-generated method stub
		
	}

	public void visitTFloatMul(TFloatMul n) {
		visitSons(n);
		// TODO Auto-generated method stub
		
	}

	public void visitTLockLE(TLockLE n) {
		visitSons(n);
		// TODO Auto-generated method stub
		
	}

	public void visitTLockLT(TLockLT n) {
		visitSons(n);
		// TODO Auto-generated method stub
		
	}

	public void visitTRefEQ(TRefEQ n) {
		visitSons(n);
		if(sonsAreBool(n)) {
			// in fact the node was wrong.
			TFunction parent = n.parent;
			int ind = parent.sons.indexOf(n);
			TBoolEQ beq = new TBoolEQ();
			for(int i = 0; i < n.sons.size(); i++) {
				TNode t = n.getChildAt(i);
				beq.sons.add(t);
			}
			parent.sons.setElementAt(beq, ind);
			beq.accept(this);
		}
		else {
			n.type = TNode.$boolean;
		}
	}

	public void visitTRefNE(TRefNE n) {
		n.type = TNode.$boolean;
		visitSons(n);
		// TODO Auto-generated method stub
		
	}

	public void visitTTypeEQ(TTypeEQ n) {
		visitSons(n);
		if(sonsAreBool(n)) {
			// in fact the node was wrong.
			TFunction parent = n.parent;
			int ind = parent.sons.indexOf(n);
			TBoolEQ beq = new TBoolEQ();
			for(int i = 0; i < n.sons.size(); i++) {
				TNode t = n.getChildAt(i);
				beq.sons.add(t);
			}
			parent.sons.setElementAt(beq, ind);
			beq.accept(this);
		}
		else {
			n.type = TNode.$boolean;
		}
	}

	public void visitTTypeNE(TTypeNE n) {
		n.type = TNode.$boolean;
		visitSons(n);
		// TODO Auto-generated method stub
		
	}

	public void visitTTypeLE(TTypeLE n) {
		n.type = TNode.$boolean;
		visitSons(n);
		// TODO Auto-generated method stub
		
	}

	public void visitTCast(TCast n) {
		visitSons(n);
		// TODO Auto-generated method stub
		
	}

	public void visitTIs(TIs n) {
		visitSons(n);
		// TODO Auto-generated method stub
		
	}

	public void visitTSelect(TSelect n) {
		visitSons(n);
		// TODO Auto-generated method stub
		
	}

	public void visitTStore(TStore n) {
		visitSons(n);
		// TODO Auto-generated method stub
		
	}

	public void visitTTypeOf(TTypeOf n) {
		visitSons(n);
		// TODO Auto-generated method stub
		
	}

	public void visitTForAll(TForAll n) {
		n.type = TNode.$boolean;
		visitSons(n);	
	}

	public void visitTExist(TExist n) {
		n.type = TNode.$boolean;
		visitSons(n);
		
	}

	public void visitTIsAllocated(TIsAllocated n) {
		visitSons(n);
		// TODO Auto-generated method stub
		
	}

	public void visitTEClosedTime(TEClosedTime n) {
		visitSons(n);
		// TODO Auto-generated method stub
		
	}

	public void visitTFClosedTime(TFClosedTime n) {
		visitSons(n);
		// TODO Auto-generated method stub
		
	}

	public void visitTAsElems(TAsElems n) {
		visitSons(n);
		// TODO Auto-generated method stub
		
	}

	public void visitTAsField(TAsField n) {
		visitSons(n);
		// TODO Auto-generated method stub
		
	}

	public void visitTAsLockSet(TAsLockSet n) {
		visitSons(n);
		// TODO Auto-generated method stub
		
	}

	public void visitTArrayLength(TArrayLength n) {
		visitSons(n);
		// TODO Auto-generated method stub
		
	}

	public void visitTArrayFresh(TArrayFresh n) {
		visitSons(n);
		// TODO Auto-generated method stub
		
	}

	public void visitTArrayShapeOne(TArrayShapeOne n) {
		visitSons(n);
		// TODO Auto-generated method stub
		
	}

	public void visitTArrayShapeMore(TArrayShapeMore n) {
		visitSons(n);
		// TODO Auto-generated method stub
		
	}

	public void visitTIsNewArray(TIsNewArray n) {
		visitSons(n);
		// TODO Auto-generated method stub
		
	}

	public void visitTUnset(TUnset n) {
		visitSons(n);
		// TODO Auto-generated method stub
		
	}

	public void visitTMethodCall(TMethodCall n) {
		visitSons(n);
	}
	
	public void visitTString(TString n) {
		n.type = TNode.$String;
	}

	public void visitTBoolean(TBoolean n) {
		n.type = TNode.$boolean;
		
	}

	public void visitTChar(TChar n) {
		n.type = TNode.$char;
	}

	public void visitTInt(TInt n) {
		n.type = TNode.$integer;
	}

	public void visitTFloat(TFloat n) {
		n.type = TNode.$float;
		
	}

	public void visitTDouble(TDouble n) {
		n.type = TNode.$double;
		
	}

	public void visitTNull(TNull n) {
		n.type = TNode.$Reference;
		
	}


	

}
