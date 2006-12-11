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
	public void visitTRoot(/*@non_null@*/ TRoot n) throws IOException {
		Iterator iter = ((List) n.sons.clone()).iterator();
		while(iter.hasNext()) {
		    ((TNode)iter.next()).accept(this);
		}
	}
	
	
	public void visitTAllocLE(/*@non_null@*/ TAllocLE n) throws IOException {
		
	}

	public void visitTAllocLT(/*@non_null@*/ TAllocLT n) throws IOException {
		
	}

	public void visitTAnyEQ(/*@non_null@*/ TAnyEQ n) throws IOException {
		
	}

	public void visitTAnyNE(/*@non_null@*/ TAnyNE n) throws IOException {
		
	}

	public void visitTArrayFresh(/*@non_null@*/ TArrayFresh n) throws IOException {
		
	}

	public void visitTArrayLength(/*@non_null@*/ TArrayLength n) throws IOException {
		
	}

	public void visitTArrayShapeMore(/*@non_null@*/ TArrayShapeMore n) throws IOException {
		
	}

	public void visitTArrayShapeOne(/*@non_null@*/ TArrayShapeOne n) throws IOException {
		
	}

	public void visitTAsElems(/*@non_null@*/ TAsElems n) throws IOException {
		
	}

	public void visitTAsField(/*@non_null@*/ TAsField n) throws IOException {
		
	}

	public void visitTAsLockSet(/*@non_null@*/ TAsLockSet n) throws IOException {
		
	}

	public void visitTBoolAnd(/*@non_null@*/ TBoolAnd n) throws IOException {
		
	}

	public void visitTBoolEQ(/*@non_null@*/ TBoolEQ n) throws IOException {
		
	}

	public void visitTBoolNE(/*@non_null@*/ TBoolNE n) throws IOException {
		
	}

	public void visitTBoolNot(/*@non_null@*/ TBoolNot n) throws IOException {
		
	}

	public void visitTBoolOr(/*@non_null@*/ TBoolOr n) throws IOException {
		
	}

	public void visitTBoolean(/*@non_null@*/ TBoolean n) throws IOException {
		
	}

	public void visitTCast(/*@non_null@*/ TCast n) throws IOException {
		
	}

	public void visitTChar(/*@non_null@*/ TChar n) throws IOException {
		
	}

	public void visitTDouble(/*@non_null@*/ TDouble n) throws IOException {
		
	}

	public void visitTEClosedTime(/*@non_null@*/ TEClosedTime n) throws IOException {
		
	}

	public void visitTExist(/*@non_null@*/ TExist n) throws IOException {
		
	}

	public void visitTFClosedTime(/*@non_null@*/ TFClosedTime n) throws IOException {
		
	}

	public void visitTFloat(/*@non_null@*/ TFloat n) throws IOException {
		
	}

	public void visitTFloatAdd(/*@non_null@*/ TFloatAdd n) throws IOException {
		
	}

	public void visitTFloatDiv(/*@non_null@*/ TFloatDiv n) throws IOException {
		
	}

	public void visitTFloatEQ(/*@non_null@*/ TFloatEQ n) throws IOException {
		
	}

	public void visitTFloatGE(/*@non_null@*/ TFloatGE n) throws IOException {
		
	}

	public void visitTFloatGT(/*@non_null@*/ TFloatGT n) throws IOException {
		
	}

	public void visitTFloatLE(/*@non_null@*/ TFloatLE n) throws IOException {
		
	}

	public void visitTFloatLT(/*@non_null@*/ TFloatLT n) throws IOException {
		
	}

	public void visitTFloatMod(/*@non_null@*/ TFloatMod n) throws IOException {
		
	}

	public void visitTFloatMul(/*@non_null@*/ TFloatMul n) throws IOException {
		
	}

	public void visitTFloatNE(/*@non_null@*/ TFloatNE n) throws IOException {
		
	}

	public void visitTForAll(/*@non_null@*/ TForAll n) throws IOException {
		
	}

	public void visitTInt(/*@non_null@*/ TInt n) throws IOException {
		
	}

	public void visitTIntegralAdd(/*@non_null@*/ TIntegralAdd n) throws IOException {
		
	}

	public void visitTIntegralDiv(/*@non_null@*/ TIntegralDiv n) throws IOException {
		
	}

	public void visitTIntegralEQ(/*@non_null@*/ TIntegralEQ n) throws IOException {
		
	}

	public void visitTIntegralGE(/*@non_null@*/ TIntegralGE n) throws IOException {
		
	}

	public void visitTIntegralGT(/*@non_null@*/ TIntegralGT n) throws IOException {
		
	}

	public void visitTIntegralLE(/*@non_null@*/ TIntegralLE n) throws IOException {
		
	}

	public void visitTIntegralLT(/*@non_null@*/ TIntegralLT n) throws IOException {
		
	}

	public void visitTIntegralMod(/*@non_null@*/ TIntegralMod n) throws IOException {
		
	}

	public void visitTIntegralMul(/*@non_null@*/ TIntegralMul n) throws IOException {
		
	}

	public void visitTIntegralNE(/*@non_null@*/ TIntegralNE n) throws IOException {
		
	}

	public void visitTIntegralSub(/*@non_null@*/ TIntegralSub sub) throws IOException {
		
	}

	public void visitTIs(/*@non_null@*/ TIs n) throws IOException {
		
	}

	public void visitTIsAllocated(/*@non_null@*/ TIsAllocated n) throws IOException {
		
	}

	public void visitTIsNewArray(/*@non_null@*/ TIsNewArray n) throws IOException {
		
	}

	public void visitTLockLE(/*@non_null@*/ TLockLE n) throws IOException {
		
	}

	public void visitTLockLT(/*@non_null@*/ TLockLT n) throws IOException {
		
	}

	public void visitTMethodCall(/*@non_null@*/ TMethodCall call) throws IOException {
		
	}

	public void visitTName(/*@non_null@*/ TName n) throws IOException {
		
	}

	public void visitTNull(/*@non_null@*/ TNull n) throws IOException {
		
	}

	public void visitTRefEQ(/*@non_null@*/ TRefEQ n) throws IOException {
		
	}

	public void visitTRefNE(/*@non_null@*/ TRefNE n) throws IOException {
		
	}

	public void visitTSelect(/*@non_null@*/ TSelect n) throws IOException {
		
	}

	public void visitTStore(/*@non_null@*/ TStore n) throws IOException {
		
	}

	public void visitTString(/*@non_null@*/ TString n) throws IOException {
		
	}

	public void visitTSum(/*@non_null@*/ TSum s) {
	
	}

	public void visitTTypeEQ(/*@non_null@*/ TTypeEQ n) throws IOException {
		
	}

	public void visitTTypeLE(/*@non_null@*/ TTypeLE n) throws IOException {
	
	}

	public void visitTTypeNE(/*@non_null@*/ TTypeNE n) throws IOException {
	
	}

	public void visitTTypeOf(/*@non_null@*/ TTypeOf n) throws IOException {
	
	}

	public void visitTUnset(/*@non_null@*/ TUnset n) throws IOException {	
	}

}
