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
			if(TNode._boolean.equals(t.type))
				return true;
		}
		return false;
	}
	
	public void visitTName(/*@non_null*/TName n) throws IOException {
	}

	public void visitTRoot(/*@non_null*/TRoot n) throws IOException {
		visitSons(n);
	}

	public void visitTBoolImplies(/*@non_null*/TBoolImplies n) throws IOException {
		n.type = TNode._boolean;
		setAllTypesTo(n, TNode._boolean);
	}

	public void visitTBoolAnd(/*@non_null*/TBoolAnd n) throws IOException {
		n.type = TNode._boolean;
		setAllTypesTo(n, TNode._boolean);
	}

	public void visitTBoolOr(/*@non_null*/TBoolOr n) throws IOException {
		n.type = TNode._boolean;
		setAllTypesTo(n, TNode._boolean);
	}

	public void visitTBoolNot(/*@non_null*/TBoolNot n) throws IOException {
		n.type = TNode._boolean;
		setAllTypesTo(n, TNode._boolean);
	}

	public void visitTBoolEQ(/*@non_null*/TBoolEQ n) throws IOException {
		n.type = TNode._boolean;
		setAllTypesTo(n, TNode._boolean);
	}

	public void visitTBoolNE(/*@non_null*/TBoolNE n) throws IOException {
		n.type = TNode._boolean;
		setAllTypesTo(n, TNode._boolean);
	}

	public void visitTAllocLT(/*@non_null*/TAllocLT n) throws IOException {
		visitSons(n);
		// TODO Auto-generated method stub
		
	}

	public void visitTAllocLE(/*@non_null*/TAllocLE n) throws IOException {
		visitSons(n);
		// TODO Auto-generated method stub
		
	}

	public void visitTAnyEQ(/*@non_null*/TAnyEQ n) throws IOException {
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
			n.type = TNode._boolean;
		}
		
	}

	public void visitTAnyNE(/*@non_null*/TAnyNE n) throws IOException {
		visitSons(n);
		n.type = TNode._boolean;
		// TODO Auto-generated method stub
		
	}

	public void visitTIntegralEQ(/*@non_null*/TIntegralEQ n) throws IOException {
		n.type = TNode._boolean;
		setAllTypesTo(n, TNode._integer);
	}

	public void visitTIntegralGE(/*@non_null*/TIntegralGE n) throws IOException {
		n.type = TNode._boolean;
		setAllTypesTo(n, TNode._integer);
	}

	public void visitTIntegralGT(/*@non_null*/TIntegralGT n) throws IOException {
		n.type = TNode._boolean;
		setAllTypesTo(n, TNode._integer);
	}

	public void visitTIntegralLE(/*@non_null*/TIntegralLE n) throws IOException {
		n.type = TNode._boolean;
		setAllTypesTo(n, TNode._integer);
		
	}

	public void visitTIntegralLT(/*@non_null*/TIntegralLT n) throws IOException {
		n.type = TNode._boolean;
		setAllTypesTo(n, TNode._integer);
		
	}

	public void visitTIntegralNE(/*@non_null*/TIntegralNE n) throws IOException {
		n.type = TNode._boolean;
		setAllTypesTo(n, TNode._integer);
	}

	public void visitTIntegralAdd(/*@non_null*/TIntegralAdd n) throws IOException {
		n.type = TNode._integer;
		setAllTypesTo(n, TNode._integer);
	}

	public void visitTIntegralDiv(/*@non_null*/TIntegralDiv n) throws IOException {
		n.type = TNode._integer;
		setAllTypesTo(n, TNode._integer);
		
	}

	public void visitTIntegralMod(/*@non_null*/TIntegralMod n) throws IOException {
		n.type = TNode._integer;
		setAllTypesTo(n, TNode._integer);
	}

	public void visitTIntegralMul(/*@non_null*/TIntegralMul n) throws IOException {
		n.type = TNode._integer;
		setAllTypesTo(n, TNode._integer);	
	}
	
	public void visitTIntegralSub(/*@non_null*/TIntegralSub n) throws IOException {
		n.type = TNode._integer;
		setAllTypesTo(n, TNode._integer);
	}

	public void visitTFloatEQ(/*@non_null*/TFloatEQ n) throws IOException {
		n.type = TNode._boolean;
		visitSons(n);
		// TODO Auto-generated method stub
		
	}

	public void visitTFloatGE(/*@non_null*/TFloatGE n) throws IOException {
		n.type = TNode._boolean;
		visitSons(n);
		// TODO Auto-generated method stub
		
	}

	public void visitTFloatGT(/*@non_null*/TFloatGT n) throws IOException {
		n.type = TNode._boolean;
		visitSons(n);
		// TODO Auto-generated method stub
		
	}

	public void visitTFloatLE(/*@non_null*/TFloatLE n) throws IOException {
		n.type = TNode._boolean;
		visitSons(n);
		// TODO Auto-generated method stub
		
	}

	public void visitTFloatLT(/*@non_null*/TFloatLT n) throws IOException {
		n.type = TNode._boolean;
		visitSons(n);
		// TODO Auto-generated method stub
		
	}

	public void visitTFloatNE(/*@non_null*/TFloatNE n) throws IOException {
		n.type = TNode._boolean;
		visitSons(n);
		// TODO Auto-generated method stub
		
	}

	public void visitTFloatAdd(/*@non_null*/TFloatAdd n) throws IOException {
		visitSons(n);
		// TODO Auto-generated method stub
		
	}

	public void visitTFloatDiv(/*@non_null*/TFloatDiv n) throws IOException {
		visitSons(n);
		// TODO Auto-generated method stub
		
	}

	public void visitTFloatMod(/*@non_null*/TFloatMod n) throws IOException {
		visitSons(n);
		// TODO Auto-generated method stub
		
	}

	public void visitTFloatMul(/*@non_null*/TFloatMul n) throws IOException {
		visitSons(n);
		// TODO Auto-generated method stub
		
	}

	public void visitTLockLE(/*@non_null*/TLockLE n) throws IOException {
		visitSons(n);
		// TODO Auto-generated method stub
		
	}

	public void visitTLockLT(/*@non_null*/TLockLT n) throws IOException {
		visitSons(n);
		// TODO Auto-generated method stub
		
	}

	public void visitTRefEQ(/*@non_null*/TRefEQ n) throws IOException {
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
			n.type = TNode._boolean;
		}
	}

	public void visitTRefNE(/*@non_null*/TRefNE n) throws IOException {
		n.type = TNode._boolean;
		visitSons(n);
		// TODO Auto-generated method stub
		
	}

	public void visitTTypeEQ(/*@non_null*/TTypeEQ n) throws IOException {
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
			n.type = TNode._boolean;
		}
	}

	public void visitTTypeNE(/*@non_null*/TTypeNE n) throws IOException {
		n.type = TNode._boolean;
		visitSons(n);
		// TODO Auto-generated method stub
		
	}

	public void visitTTypeLE(/*@non_null*/TTypeLE n) throws IOException {
		n.type = TNode._boolean;
		visitSons(n);
		// TODO Auto-generated method stub
		
	}

	public void visitTCast(/*@non_null*/TCast n) throws IOException {
		visitSons(n);
		// TODO Auto-generated method stub
		
	}

	public void visitTIs(/*@non_null*/TIs n) throws IOException {
		visitSons(n);
		// TODO Auto-generated method stub
		
	}

	public void visitTSelect(/*@non_null*/TSelect n) throws IOException {
		visitSons(n);
		// TODO Auto-generated method stub
		
	}

	public void visitTStore(/*@non_null*/TStore n) throws IOException {
		visitSons(n);
		// TODO Auto-generated method stub
		
	}

	public void visitTTypeOf(/*@non_null*/TTypeOf n) throws IOException {
		visitSons(n);
		// TODO Auto-generated method stub
		
	}

	public void visitTForAll(/*@non_null*/TForAll n) throws IOException {
		n.type = TNode._boolean;
		visitSons(n);	
	}

	public void visitTExist(/*@non_null*/TExist n) throws IOException {
		n.type = TNode._boolean;
		visitSons(n);
		
	}

	public void visitTIsAllocated(/*@non_null*/TIsAllocated n) throws IOException {
		visitSons(n);
		// TODO Auto-generated method stub
		
	}

	public void visitTEClosedTime(/*@non_null*/TEClosedTime n) throws IOException {
		visitSons(n);
		// TODO Auto-generated method stub
		
	}

	public void visitTFClosedTime(/*@non_null*/TFClosedTime n) throws IOException {
		visitSons(n);
		// TODO Auto-generated method stub
		
	}

	public void visitTAsElems(/*@non_null*/TAsElems n) throws IOException {
		visitSons(n);
		// TODO Auto-generated method stub
		
	}

	public void visitTAsField(/*@non_null*/TAsField n) throws IOException {
		visitSons(n);
		// TODO Auto-generated method stub
		
	}

	public void visitTAsLockSet(/*@non_null*/TAsLockSet n) throws IOException {
		visitSons(n);
		// TODO Auto-generated method stub
		
	}

	public void visitTArrayLength(/*@non_null*/TArrayLength n) throws IOException {
		visitSons(n);
		// TODO Auto-generated method stub
		
	}

	public void visitTArrayFresh(/*@non_null*/TArrayFresh n) throws IOException {
		visitSons(n);
		// TODO Auto-generated method stub
		
	}

	public void visitTArrayShapeOne(/*@non_null*/TArrayShapeOne n) throws IOException {
		visitSons(n);
		// TODO Auto-generated method stub
		
	}

	public void visitTArrayShapeMore(/*@non_null*/TArrayShapeMore n) throws IOException {
		visitSons(n);
		// TODO Auto-generated method stub
		
	}

	public void visitTIsNewArray(/*@non_null*/TIsNewArray n) throws IOException {
		visitSons(n);
		// TODO Auto-generated method stub
		
	}

	public void visitTUnset(/*@non_null*/TUnset n) throws IOException {
		visitSons(n);
		// TODO Auto-generated method stub
		
	}

	public void visitTMethodCall(/*@non_null*/TMethodCall n) throws IOException {
		visitSons(n);
	}
	
	public void visitTString(/*@non_null*/TString n) throws IOException {
		n.type = TNode._String;
	}

	public void visitTBoolean(/*@non_null*/TBoolean n) throws IOException {
		n.type = TNode._boolean;
		
	}

	public void visitTChar(/*@non_null*/TChar n) throws IOException {
		n.type = TNode._char;
	}

	public void visitTInt(/*@non_null*/TInt n) throws IOException {
		n.type = TNode._integer;
	}

	public void visitTFloat(/*@non_null*/TFloat n) throws IOException {
		n.type = TNode._float;
		
	}

	public void visitTDouble(/*@non_null*/TDouble n) throws IOException {
		n.type = TNode._double;
		
	}

	public void visitTNull(/*@non_null*/TNull n) throws IOException {
		n.type = TNode._Reference;
		
	}

	public void visitTSum(TSum s) {
		// TODO Auto-generated method stub
		
	}


	

}
