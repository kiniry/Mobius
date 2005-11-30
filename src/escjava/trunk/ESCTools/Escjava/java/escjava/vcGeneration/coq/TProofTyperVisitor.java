package escjava.vcGeneration.coq;

import java.io.*;

import escjava.vcGeneration.*;

/**
 * Coq extension needs 'clear' typing.
 * This retyping is done using the known function signatures.
 * This is done without any subtleties.
 * @author J. Charles
 * @version last update: 15/11/2005
 */
public class TProofTyperVisitor extends TVisitor {

    TProofTyperVisitor() {
        // Since this visitor modifies the original tree, it has no need to output to a stream
        super(null);
    }
    
	public void setAllTypesTo(TFunction f, TypeInfo ti) throws IOException {
		for(int i = 0; i < f.sons.size(); i++) {
			TNode t = f.getChildAt(i);
			t.type = ti;
			t.accept(this);
		}
	}
	public void visitSons(TFunction f) throws IOException {
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
	
	public void visitTName(TName n) throws IOException {
	}

	public void visitTRoot(TRoot n) throws IOException {
		visitSons(n);
	}

	public void visitTBoolImplies(TBoolImplies n) throws IOException {
		n.type = TNode.$boolean;
		setAllTypesTo(n, TNode.$boolean);
	}

	public void visitTBoolAnd(TBoolAnd n) throws IOException {
		n.type = TNode.$boolean;
		setAllTypesTo(n, TNode.$boolean);
	}

	public void visitTBoolOr(TBoolOr n) throws IOException {
		n.type = TNode.$boolean;
		setAllTypesTo(n, TNode.$boolean);
	}

	public void visitTBoolNot(TBoolNot n) throws IOException {
		n.type = TNode.$boolean;
		setAllTypesTo(n, TNode.$boolean);
	}

	public void visitTBoolEQ(TBoolEQ n) throws IOException {
		n.type = TNode.$boolean;
		setAllTypesTo(n, TNode.$boolean);
	}

	public void visitTBoolNE(TBoolNE n) throws IOException {
		n.type = TNode.$boolean;
		setAllTypesTo(n, TNode.$boolean);
	}

	public void visitTAllocLT(TAllocLT n) throws IOException {
		visitSons(n);
		// TODO Auto-generated method stub
		
	}

	public void visitTAllocLE(TAllocLE n) throws IOException {
		visitSons(n);
		// TODO Auto-generated method stub
		
	}

	public void visitTAnyEQ(TAnyEQ n) throws IOException {
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

	public void visitTAnyNE(TAnyNE n) throws IOException {
		visitSons(n);
		n.type = TNode.$boolean;
		// TODO Auto-generated method stub
		
	}

	public void visitTIntegralEQ(TIntegralEQ n) throws IOException {
		n.type = TNode.$boolean;
		setAllTypesTo(n, TNode.$integer);
	}

	public void visitTIntegralGE(TIntegralGE n) throws IOException {
		n.type = TNode.$boolean;
		setAllTypesTo(n, TNode.$integer);
	}

	public void visitTIntegralGT(TIntegralGT n) throws IOException {
		n.type = TNode.$boolean;
		setAllTypesTo(n, TNode.$integer);
	}

	public void visitTIntegralLE(TIntegralLE n) throws IOException {
		n.type = TNode.$boolean;
		setAllTypesTo(n, TNode.$integer);
		
	}

	public void visitTIntegralLT(TIntegralLT n) throws IOException {
		n.type = TNode.$boolean;
		setAllTypesTo(n, TNode.$integer);
		
	}

	public void visitTIntegralNE(TIntegralNE n) throws IOException {
		n.type = TNode.$boolean;
		setAllTypesTo(n, TNode.$integer);
	}

	public void visitTIntegralAdd(TIntegralAdd n) throws IOException {
		n.type = TNode.$integer;
		setAllTypesTo(n, TNode.$integer);
	}

	public void visitTIntegralDiv(TIntegralDiv n) throws IOException {
		n.type = TNode.$integer;
		setAllTypesTo(n, TNode.$integer);
		
	}

	public void visitTIntegralMod(TIntegralMod n) throws IOException {
		n.type = TNode.$integer;
		setAllTypesTo(n, TNode.$integer);
	}

	public void visitTIntegralMul(TIntegralMul n) throws IOException {
		n.type = TNode.$integer;
		setAllTypesTo(n, TNode.$integer);	
	}
	
	public void visitTIntegralSub(TIntegralSub n) throws IOException {
		n.type = TNode.$integer;
		setAllTypesTo(n, TNode.$integer);
	}

	public void visitTFloatEQ(TFloatEQ n) throws IOException {
		n.type = TNode.$boolean;
		visitSons(n);
		// TODO Auto-generated method stub
		
	}

	public void visitTFloatGE(TFloatGE n) throws IOException {
		n.type = TNode.$boolean;
		visitSons(n);
		// TODO Auto-generated method stub
		
	}

	public void visitTFloatGT(TFloatGT n) throws IOException {
		n.type = TNode.$boolean;
		visitSons(n);
		// TODO Auto-generated method stub
		
	}

	public void visitTFloatLE(TFloatLE n) throws IOException {
		n.type = TNode.$boolean;
		visitSons(n);
		// TODO Auto-generated method stub
		
	}

	public void visitTFloatLT(TFloatLT n) throws IOException {
		n.type = TNode.$boolean;
		visitSons(n);
		// TODO Auto-generated method stub
		
	}

	public void visitTFloatNE(TFloatNE n) throws IOException {
		n.type = TNode.$boolean;
		visitSons(n);
		// TODO Auto-generated method stub
		
	}

	public void visitTFloatAdd(TFloatAdd n) throws IOException {
		visitSons(n);
		// TODO Auto-generated method stub
		
	}

	public void visitTFloatDiv(TFloatDiv n) throws IOException {
		visitSons(n);
		// TODO Auto-generated method stub
		
	}

	public void visitTFloatMod(TFloatMod n) throws IOException {
		visitSons(n);
		// TODO Auto-generated method stub
		
	}

	public void visitTFloatMul(TFloatMul n) throws IOException {
		visitSons(n);
		// TODO Auto-generated method stub
		
	}

	public void visitTLockLE(TLockLE n) throws IOException {
		visitSons(n);
		// TODO Auto-generated method stub
		
	}

	public void visitTLockLT(TLockLT n) throws IOException {
		visitSons(n);
		// TODO Auto-generated method stub
		
	}

	public void visitTRefEQ(TRefEQ n) throws IOException {
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

	public void visitTRefNE(TRefNE n) throws IOException {
		n.type = TNode.$boolean;
		visitSons(n);
		// TODO Auto-generated method stub
		
	}

	public void visitTTypeEQ(TTypeEQ n) throws IOException {
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

	public void visitTTypeNE(TTypeNE n) throws IOException {
		n.type = TNode.$boolean;
		visitSons(n);
		// TODO Auto-generated method stub
		
	}

	public void visitTTypeLE(TTypeLE n) throws IOException {
		n.type = TNode.$boolean;
		visitSons(n);
		// TODO Auto-generated method stub
		
	}

	public void visitTCast(TCast n) throws IOException {
		visitSons(n);
		// TODO Auto-generated method stub
		
	}

	public void visitTIs(TIs n) throws IOException {
		visitSons(n);
		// TODO Auto-generated method stub
		
	}

	public void visitTSelect(TSelect n) throws IOException {
		visitSons(n);
		// TODO Auto-generated method stub
		
	}

	public void visitTStore(TStore n) throws IOException {
		visitSons(n);
		// TODO Auto-generated method stub
		
	}

	public void visitTTypeOf(TTypeOf n) throws IOException {
		visitSons(n);
		// TODO Auto-generated method stub
		
	}

	public void visitTForAll(TForAll n) throws IOException {
		n.type = TNode.$boolean;
		visitSons(n);	
	}

	public void visitTExist(TExist n) throws IOException {
		n.type = TNode.$boolean;
		visitSons(n);
		
	}

	public void visitTIsAllocated(TIsAllocated n) throws IOException {
		visitSons(n);
		// TODO Auto-generated method stub
		
	}

	public void visitTEClosedTime(TEClosedTime n) throws IOException {
		visitSons(n);
		// TODO Auto-generated method stub
		
	}

	public void visitTFClosedTime(TFClosedTime n) throws IOException {
		visitSons(n);
		// TODO Auto-generated method stub
		
	}

	public void visitTAsElems(TAsElems n) throws IOException {
		visitSons(n);
		// TODO Auto-generated method stub
		
	}

	public void visitTAsField(TAsField n) throws IOException {
		visitSons(n);
		// TODO Auto-generated method stub
		
	}

	public void visitTAsLockSet(TAsLockSet n) throws IOException {
		visitSons(n);
		// TODO Auto-generated method stub
		
	}

	public void visitTArrayLength(TArrayLength n) throws IOException {
		visitSons(n);
		// TODO Auto-generated method stub
		
	}

	public void visitTArrayFresh(TArrayFresh n) throws IOException {
		visitSons(n);
		// TODO Auto-generated method stub
		
	}

	public void visitTArrayShapeOne(TArrayShapeOne n) throws IOException {
		visitSons(n);
		// TODO Auto-generated method stub
		
	}

	public void visitTArrayShapeMore(TArrayShapeMore n) throws IOException {
		visitSons(n);
		// TODO Auto-generated method stub
		
	}

	public void visitTIsNewArray(TIsNewArray n) throws IOException {
		visitSons(n);
		// TODO Auto-generated method stub
		
	}

	public void visitTUnset(TUnset n) throws IOException {
		visitSons(n);
		// TODO Auto-generated method stub
		
	}

	public void visitTMethodCall(TMethodCall n) throws IOException {
		visitSons(n);
	}
	
	public void visitTString(TString n) throws IOException {
		n.type = TNode.$String;
	}

	public void visitTBoolean(TBoolean n) throws IOException {
		n.type = TNode.$boolean;
		
	}

	public void visitTChar(TChar n) throws IOException {
		n.type = TNode.$char;
	}

	public void visitTInt(TInt n) throws IOException {
		n.type = TNode.$integer;
	}

	public void visitTFloat(TFloat n) throws IOException {
		n.type = TNode.$float;
		
	}

	public void visitTDouble(TDouble n) throws IOException {
		n.type = TNode.$double;
		
	}

	public void visitTNull(TNull n) throws IOException {
		n.type = TNode.$Reference;
		
	}


	

}
