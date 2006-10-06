package escjava.vcGeneration.coq.visitor.simplifiers;

import java.io.IOException;
import java.util.Iterator;
import java.util.List;
import java.util.Vector;

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
import escjava.vcGeneration.TVisitor;

/**
 * A class giving the basic functionnality for the simplifiers.
 * @author J. Charles
 */
public abstract class ATSimplifier extends TVisitor {
	
	/**
	 * The empty constructor. Usable only if the inheriting class
	 * doesn't want to write any result to the output stream 
	 * (this is the case for the simplifiers).
	 */
	public ATSimplifier() {
		super(null);
	}
	
	
	/**
	 * Find the root node from a random node from a term.
	 * @param node the node from which to search the root from
	 * @return the root of the term
	 */
	public static TFunction findRoot(TFunction node) {
		if(node.parent == null)
			return node;
		while(node.parent.parent != null)
			node = node.parent;
		return node;
	}
	
	
	/**
	 * Clone the argument (do not clone the other nodes linked)
	 * @param nod the node to clone
	 * @return the clone
	 */
	public static TBoolImplies cloneof(TBoolImplies nod) {
		TBoolImplies tbi = new TBoolImplies();
		tbi.sons = new Vector();
		tbi.sons.add(nod.sons.get(0));
		tbi.sons.add(nod.sons.get(1));
		tbi.type = nod.type;
		tbi.parent = nod.parent;
		return tbi;
	}
	
	/**
	 * Add a son at the right position to a node.
	 * @param parent the node to add the child to
	 * @param pos the position to add the child to
	 * @param son th child to add
	 */
	public static void addSon(TFunction parent, int pos, TNode son) {
		if(parent.sons.size() <= pos) {
			parent.sons.setSize(pos +1);
		}
		parent.sons.set(pos, son);
		son.parent = parent;
	}
	
	
	/**
	 * Visit all the children from the root node given as a parameter.
	 */
	/*
	 * (non-Javadoc)
	 * @see escjava.vcGeneration.TVisitor#visitTRoot(escjava.vcGeneration.TRoot)
	 */
	public void visitTRoot(TRoot n) throws IOException {
		Iterator iter = ((List) n.sons.clone()).iterator();
		while(iter.hasNext()) {
		    ((TNode)iter.next()).accept(this);
		}
	}
	
	
	public void visitTAllocLE(TAllocLE n) throws IOException {
		
	}

	public void visitTAllocLT(TAllocLT n) throws IOException {
		
	}

	public void visitTAnyEQ(TAnyEQ n) throws IOException {
		
	}

	public void visitTAnyNE(TAnyNE n) throws IOException {
		
	}

	public void visitTArrayFresh(TArrayFresh n) throws IOException {
		
	}

	public void visitTArrayLength(TArrayLength n) throws IOException {
		
	}

	public void visitTArrayShapeMore(TArrayShapeMore n) throws IOException {
		
	}

	public void visitTArrayShapeOne(TArrayShapeOne n) throws IOException {
		
	}

	public void visitTAsElems(TAsElems n) throws IOException {
		
	}

	public void visitTAsField(TAsField n) throws IOException {
		
	}

	public void visitTAsLockSet(TAsLockSet n) throws IOException {
		
	}

	public void visitTBoolAnd(TBoolAnd n) throws IOException {
		
	}

	public void visitTBoolEQ(TBoolEQ n) throws IOException {
		
	}

	public void visitTBoolNE(TBoolNE n) throws IOException {
		
	}

	public void visitTBoolNot(TBoolNot n) throws IOException {
		
	}

	public void visitTBoolOr(TBoolOr n) throws IOException {
		
	}

	public void visitTBoolean(TBoolean n) throws IOException {
		
	}

	public void visitTCast(TCast n) throws IOException {
		
	}

	public void visitTChar(TChar n) throws IOException {
		
	}

	public void visitTDouble(TDouble n) throws IOException {
		
	}

	public void visitTEClosedTime(TEClosedTime n) throws IOException {
		
	}

	public void visitTExist(TExist n) throws IOException {
		
	}

	public void visitTFClosedTime(TFClosedTime n) throws IOException {
		
	}

	public void visitTFloat(TFloat n) throws IOException {
		
	}

	public void visitTFloatAdd(TFloatAdd n) throws IOException {
		
	}

	public void visitTFloatDiv(TFloatDiv n) throws IOException {
		
	}

	public void visitTFloatEQ(TFloatEQ n) throws IOException {
		
	}

	public void visitTFloatGE(TFloatGE n) throws IOException {
		
	}

	public void visitTFloatGT(TFloatGT n) throws IOException {
		
	}

	public void visitTFloatLE(TFloatLE n) throws IOException {
		
	}

	public void visitTFloatLT(TFloatLT n) throws IOException {
		
	}

	public void visitTFloatMod(TFloatMod n) throws IOException {
		
	}

	public void visitTFloatMul(TFloatMul n) throws IOException {
		
	}

	public void visitTFloatNE(TFloatNE n) throws IOException {
		
	}

	public void visitTForAll(TForAll n) throws IOException {
		
	}

	public void visitTInt(TInt n) throws IOException {
		
	}

	public void visitTIntegralAdd(TIntegralAdd n) throws IOException {
		
	}

	public void visitTIntegralDiv(TIntegralDiv n) throws IOException {
		
	}

	public void visitTIntegralEQ(TIntegralEQ n) throws IOException {
		
	}

	public void visitTIntegralGE(TIntegralGE n) throws IOException {
		
	}

	public void visitTIntegralGT(TIntegralGT n) throws IOException {
		
	}

	public void visitTIntegralLE(TIntegralLE n) throws IOException {
		
	}

	public void visitTIntegralLT(TIntegralLT n) throws IOException {
		
	}

	public void visitTIntegralMod(TIntegralMod n) throws IOException {
		
	}

	public void visitTIntegralMul(TIntegralMul n) throws IOException {
		
	}

	public void visitTIntegralNE(TIntegralNE n) throws IOException {
		
	}

	public void visitTIntegralSub(TIntegralSub sub) throws IOException {
		
	}

	public void visitTIs(TIs n) throws IOException {
		
	}

	public void visitTIsAllocated(TIsAllocated n) throws IOException {
		
	}

	public void visitTIsNewArray(TIsNewArray n) throws IOException {
		
	}

	public void visitTLockLE(TLockLE n) throws IOException {
		
	}

	public void visitTLockLT(TLockLT n) throws IOException {
		
	}

	public void visitTMethodCall(TMethodCall call) throws IOException {
		
	}

	public void visitTName(TName n) throws IOException {
		
	}

	public void visitTNull(TNull n) throws IOException {
		
	}

	public void visitTRefEQ(TRefEQ n) throws IOException {
		
	}

	public void visitTRefNE(TRefNE n) throws IOException {
		
	}

	public void visitTSelect(TSelect n) throws IOException {
		
	}

	public void visitTStore(TStore n) throws IOException {
		
	}

	public void visitTString(TString n) throws IOException {
		
	}

	public void visitTSum(TSum s) {
	
	}

	public void visitTTypeEQ(TTypeEQ n) throws IOException {
		
	}

	public void visitTTypeLE(TTypeLE n) throws IOException {
	
	}

	public void visitTTypeNE(TTypeNE n) throws IOException {
	
	}

	public void visitTTypeOf(TTypeOf n) throws IOException {
	
	}

	public void visitTUnset(TUnset n) throws IOException {	
	}

}
