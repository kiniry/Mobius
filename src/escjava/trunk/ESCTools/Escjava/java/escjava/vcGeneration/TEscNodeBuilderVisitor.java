package escjava.vcGeneration;

import java.util.Hashtable;

import javafe.util.Assert;
import escjava.vcGeneration.EscNodeBuilder.SArray;
import escjava.vcGeneration.EscNodeBuilder.SElems;
import escjava.vcGeneration.EscNodeBuilder.SField;
import escjava.vcGeneration.EscNodeBuilder.SLock;
import escjava.vcGeneration.EscNodeBuilder.SLockSet;
import escjava.vcGeneration.EscNodeBuilder.SShape;
import escjava.vcGeneration.EscNodeBuilder.STime;
import escjava.vcGeneration.EscNodeBuilder.SType;
import escjava.vcGeneration.NodeBuilder.SAny;
import escjava.vcGeneration.NodeBuilder.FnSymbol;
import escjava.vcGeneration.NodeBuilder.SInt;
import escjava.vcGeneration.NodeBuilder.SMap;
import escjava.vcGeneration.NodeBuilder.SPred;
import escjava.vcGeneration.NodeBuilder.QuantVar;
import escjava.vcGeneration.NodeBuilder.SReal;
import escjava.vcGeneration.NodeBuilder.SRef;
import escjava.vcGeneration.NodeBuilder.STerm;
import escjava.vcGeneration.NodeBuilder.SValue;
import escjava.vcGeneration.NodeBuilder.Sort;


public class TEscNodeBuilderVisitor extends TVisitor
{
	EscNodeBuilder builder;
	SAny result;
	SPred resultPred;
	Hashtable quantifiedVariables = new Hashtable();
	Hashtable constants = new Hashtable();
	
	public TEscNodeBuilderVisitor()
	{
		super(null);
	}

	SAny recurse(TNode n)
	{
		resultPred = null;
		result = null;
		n.accept(this);
		SAny tmp = result;
		result = null;
		Assert.notFalse(tmp != null);
		return tmp;
	}

	SPred recursePred(TNode n)
	{
		result = null;
		resultPred = null;
		n.accept(this);
		SPred tmp = resultPred;
		resultPred = null;
		Assert.notFalse(tmp != null);
		return tmp;
	}

	Sort mapSort(TypeInfo ti)
	{
		if (ti == TNode._Reference)
			return builder.sortRef;
		else if (ti == TNode._Type)
			return builder.sortType;
		else if (ti == TNode._boolean)
			return builder.sortBool;
		else if (ti == TNode._DOUBLETYPE || ti == TNode._double || ti == TNode._float)
			return builder.sortReal;
		else if (ti == TNode._char || ti == TNode._integer || ti == TNode._INTTYPE)
			return builder.sortInt;
		else if (ti == TNode._Field)
			return builder.sortField;
		else if (ti == TNode._String)
			return builder.sortString;
		else if (ti == TNode._Time)
			return builder.sortTime;
		else if (ti == TNode._Path)
			return builder.sortRef; // ???
		else
			// FIXME: do something here
			return builder.sortRef;
	}

	public void visitTName(/*@ non_null @*/TName n)
	{
		VariableInfo vi = TNode.getVariableInfo(n.name);
		if (quantifiedVariables.containsKey(vi))
			result = builder.buildQVarRef((QuantVar)quantifiedVariables.get(vi));
		else {
			if (!constants.containsKey(vi))
				constants.put(vi, builder.registerConstant(n.name, mapSort(vi.type)));
			result = builder.buildConstantRef((FnSymbol)constants.get(vi));
		}
	}
	
	
	public void visitTRoot(/*@ non_null @*/TRoot n)
	{
		Assert.notFalse(n.sons.size() == 1);
		result = recurse(n.getChildAt(0));
	}
	
	public void visitTBoolImplies(/*@ non_null @*/TBoolImplies n)
	{
		Assert.notFalse(n.sons.size() == 2);
		resultPred = builder.buildImplies(
						recursePred(n.getChildAt(0)), 
					    recursePred(n.getChildAt(1)));
	}
	
	public void visitTBoolAnd(/*@ non_null @*/TBoolAnd n)
	{
		if (n.sons.size() == 1)
			resultPred = recursePred(n.getChildAt(0));
		else {
			Assert.notFalse(n.sons.size() > 1);
			SPred[] args = new SPred[n.sons.size()];
			for (int i = 0; i < n.sons.size(); ++i)
				args[i] = recursePred(n.getChildAt(i));
			resultPred = builder.buildAnd(args);
		}
		
	}
	
	public void visitTBoolOr(/*@ non_null @*/TBoolOr n)
	{
		if (n.sons.size() == 1)
			resultPred = recursePred(n.getChildAt(0));
		else {
			Assert.notFalse(n.sons.size() > 1);
			SPred[] args = new SPred[n.sons.size()];
			for (int i = 0; i < n.sons.size(); ++i)
				args[i] = recursePred(n.getChildAt(i));
			resultPred = builder.buildOr(args);
		}
	}
	
	
	public void visitTBoolNot(/*@ non_null @*/TBoolNot n) 
	{
		Assert.notFalse(n.sons.size() == 1);
		resultPred = builder.buildNot(recursePred(n.getChildAt(0)));		
	}
	
	public void visitTBoolEQ(/*@ non_null @*/TBoolEQ n) 
	{
		Assert.notFalse(n.sons.size() == 2);
		resultPred = builder.buildIff(
						recursePred(n.getChildAt(0)), 
					    recursePred(n.getChildAt(1)));
	}
	
	public void visitTBoolNE(/*@ non_null @*/TBoolNE n)  {
		Assert.notFalse(n.sons.size() == 2);
		resultPred = builder.buildXor(
						recursePred(n.getChildAt(0)), 
					    recursePred(n.getChildAt(1)));
	}
	
	public void visitTAllocLT(/*@ non_null @*/TAllocLT n)  {
		Assert.notFalse(n.sons.size() == 2);
		resultPred = builder.buildAllocLT(
						(STime)recurse(n.getChildAt(0)), 
						(STime)recurse(n.getChildAt(1)));
	}
	
	public void visitTAllocLE(/*@ non_null @*/TAllocLE n)  {
		Assert.notFalse(n.sons.size() == 2);
		resultPred = builder.buildAllocLE(
						(STime)recurse(n.getChildAt(0)), 
						(STime)recurse(n.getChildAt(1)));
	}
	
	public void visitTAnyEQ(/*@ non_null @*/TAnyEQ n)
	{
		Assert.notFalse(n.sons.size() == 2);
		resultPred = builder.buildAnyEQ(
						recurse(n.getChildAt(0)), 
						recurse(n.getChildAt(1)));
	}
	
	public void visitTAnyNE(/*@ non_null @*/TAnyNE n)
	{
		Assert.notFalse(n.sons.size() == 2);
		resultPred = builder.buildAnyNE(
						recurse(n.getChildAt(0)), 
						recurse(n.getChildAt(1)));
	}
	
	void intPred(int op, TIntOp n)
	{
		Assert.notFalse(n.sons.size() == 2);
		resultPred = builder.buildIntPred(op,
						(SInt)recurse(n.getChildAt(0)), 
						(SInt)recurse(n.getChildAt(1)));
	}
	
	void intFun(int op, TIntFun n)
	{
		Assert.notFalse(n.sons.size() == 2);
		result = builder.buildIntFun(op,
						(SInt)recurse(n.getChildAt(0)), 
						(SInt)recurse(n.getChildAt(1)));
	}
	
	public void visitTIntegralEQ(/*@ non_null @*/TIntegralEQ n) { intPred(builder.predEQ, n); }	
	public void visitTIntegralNE(/*@ non_null @*/TIntegralNE n) { intPred(builder.predNE, n); }	
	public void visitTIntegralGE(/*@ non_null @*/TIntegralGE n) { intPred(builder.predGE, n); }
	public void visitTIntegralGT(/*@ non_null @*/TIntegralGT n) { intPred(builder.predGT, n); }
	public void visitTIntegralLE(/*@ non_null @*/TIntegralLE n) { intPred(builder.predLE, n); }
	public void visitTIntegralLT(/*@ non_null @*/TIntegralLT n) { intPred(builder.predLT, n); }
	
	public void visitTIntegralAdd(/*@ non_null @*/TIntegralAdd n) { intFun(builder.funADD, n); }
	public void visitTIntegralDiv(/*@ non_null @*/TIntegralDiv n) { intFun(builder.funDIV, n); }
	public void visitTIntegralMod(/*@ non_null @*/TIntegralMod n) { intFun(builder.funMOD, n); }
	public void visitTIntegralMul(/*@ non_null @*/TIntegralMul n) { intFun(builder.funMUL, n); }
	public void visitTIntegralSub(/*@ non_null @*/TIntegralSub n) { intFun(builder.funSUB, n); }
	
	void realPred(int op, TFloatOp n)
	{
		Assert.notFalse(n.sons.size() == 2);
		resultPred = builder.buildRealPred(op,
						(SReal)recurse(n.getChildAt(0)), 
						(SReal)recurse(n.getChildAt(1)));
	}
	
	void realFun(int op, TFloatFun n)
	{
		Assert.notFalse(n.sons.size() == 2);
		result = builder.buildRealFun(op,
						(SReal)recurse(n.getChildAt(0)), 
						(SReal)recurse(n.getChildAt(1)));
	}
	
	public void visitTFloatEQ(/*@ non_null @*/TFloatEQ n) { realPred(builder.predEQ, n); }
	public void visitTFloatGE(/*@ non_null @*/TFloatGE n) { realPred(builder.predGE, n); }
	public void visitTFloatGT(/*@ non_null @*/TFloatGT n) { realPred(builder.predGT, n); }
	public void visitTFloatLE(/*@ non_null @*/TFloatLE n) { realPred(builder.predLE, n); }
	public void visitTFloatLT(/*@ non_null @*/TFloatLT n) { realPred(builder.predLT, n); }
	public void visitTFloatNE(/*@ non_null @*/TFloatNE n) { realPred(builder.predNE, n); }
	
	public void visitTFloatAdd(/*@ non_null @*/TFloatAdd n) { realFun(builder.funADD, n); }
	public void visitTFloatDiv(/*@ non_null @*/TFloatDiv n) { realFun(builder.funDIV, n); }
	public void visitTFloatMod(/*@ non_null @*/TFloatMod n) { realFun(builder.funMOD, n); }
	public void visitTFloatMul(/*@ non_null @*/TFloatMul n) { realFun(builder.funMUL, n); }
	// TODO wtf? no sub?
	//public void visitTFloatSub(/*@ non_null @*/TFloatSub n) { realFun(builder.funSUB, n); }
	
	public void visitTLockLE(/*@ non_null @*/TLockLE n)
	{
		Assert.notFalse(n.sons.size() == 2);
		resultPred = builder.buildLockLE(
						(SLock)recurse(n.getChildAt(0)), 
						(SLock)recurse(n.getChildAt(1)));	
	}
	
	public void visitTLockLT(/*@ non_null @*/TLockLT n)
	{
		Assert.notFalse(n.sons.size() == 2);
		resultPred = builder.buildLockLT(
						(SLock)recurse(n.getChildAt(0)), 
						(SLock)recurse(n.getChildAt(1)));	
	}
	
	public void visitTRefEQ(/*@ non_null @*/TRefEQ n)
	{
		Assert.notFalse(n.sons.size() == 2);
		resultPred = builder.buildRefEQ(
						(SRef)recurse(n.getChildAt(0)), 
						(SRef)recurse(n.getChildAt(1)));		
	}
	
	public void visitTRefNE(/*@ non_null @*/TRefNE n)
	{
		Assert.notFalse(n.sons.size() == 2);
		resultPred = builder.buildRefNE(
						(SRef)recurse(n.getChildAt(0)), 
						(SRef)recurse(n.getChildAt(1)));		
	}
	
	public void visitTTypeEQ(/*@ non_null @*/TTypeEQ n)
	{
		Assert.notFalse(n.sons.size() == 2);
		resultPred = builder.buildTypeEQ(
						(SType)recurse(n.getChildAt(0)), 
						(SType)recurse(n.getChildAt(1)));		
	}
	
	public void visitTTypeNE(/*@ non_null @*/TTypeNE n)
	{
		Assert.notFalse(n.sons.size() == 2);
		resultPred = builder.buildTypeNE(
						(SType)recurse(n.getChildAt(0)), 
						(SType)recurse(n.getChildAt(1)));		
	}
	
	public void visitTTypeLE(/*@ non_null @*/TTypeLE n)
	{
		Assert.notFalse(n.sons.size() == 2);
		resultPred = builder.buildTypeLE(
						(SType)recurse(n.getChildAt(0)), 
						(SType)recurse(n.getChildAt(1)));		
	}
	
	public void visitTCast(/*@ non_null @*/TCast n)
	{
		Assert.notFalse(n.sons.size() == 2);
		result = builder.buildCast(
						(SValue)recurse(n.getChildAt(0)), 
						(SType)recurse(n.getChildAt(1)));		
	}
	
	public void visitTIs(/*@ non_null @*/TIs n)
	{
		Assert.notFalse(n.sons.size() == 2);
		resultPred = builder.buildIs(
						(SValue)recurse(n.getChildAt(0)), 
						(SType)recurse(n.getChildAt(1)));		
	}
	
	public void visitTTypeOf(/*@ non_null @*/TTypeOf n)
	{
		Assert.notFalse(n.sons.size() == 2);
		result = builder.buildTypeOf(
						(SValue)recurse(n.getChildAt(0)));		
	}
	
	public void visitTSelect(/*@ non_null @*/TSelect n)
	{
		Assert.notFalse(n.sons.size() == 2);
		result = builder.buildSelect(
						(SMap)recurse(n.getChildAt(0)), 
						(SValue)recurse(n.getChildAt(1)));			
	}
	
	public void visitTStore(/*@ non_null @*/TStore n)
	{
		Assert.notFalse(n.sons.size() == 2);
		result = builder.buildStore(
						(SMap)recurse(n.getChildAt(0)), 
						(SValue)recurse(n.getChildAt(1)),
						(SValue)recurse(n.getChildAt(2))
						);			
	}
	
	void visitQuant(boolean exists, TBoolRes n)
	{
		int i;
		
		for (i = 0; i < n.sons.size(); ++i)
			if (! (n.getChildAt(i) instanceof TName))
				break;
		
		TName[] names = new TName[i];
		VariableInfo[] infos = new  VariableInfo[i];
		QuantVar[] backup = new QuantVar[i];
		QuantVar[] current = new QuantVar[i];
		
		for (i = 0; i < n.sons.size(); ++i) {
			if (! (n.getChildAt(i) instanceof TName))
				break;
			names[i] = (TName)n.getChildAt(i);
			infos[i] = TNode.getVariableInfo(names[i].name);
			if (quantifiedVariables.containsKey(infos[i]))
				backup[i] = (QuantVar)quantifiedVariables.get(infos[i]);
			QuantVar v = builder.registerQuantifiedVariable(names[i].name, mapSort(infos[i].type));
			quantifiedVariables.put(infos[i], v);
			current[i] = v;
		}
		
		if (exists)
			resultPred = builder.buildExists(current, recursePred(n.getChildAt(i)));
		else
			resultPred = builder.buildForAll(current, recursePred(n.getChildAt(i)),
											 new STerm[0][0], new STerm[0]);
		
		i++;
		Assert.notFalse(i == n.sons.size());
		
		for (int j = 0; j < backup.length; ++i) {
			quantifiedVariables.remove(infos[i]);
			if (backup[i] != null)
				quantifiedVariables.put(infos[i], backup[i]);
		}
	}
	
	public void visitTForAll(/*@ non_null @*/TForAll n) { visitQuant(false, n); }	
	public void visitTExist(/*@ non_null @*/TExist n) { visitQuant(true, n); }
	
	public void visitTIsAllocated(/*@ non_null @*/TIsAllocated n)
	{
		Assert.notFalse(n.sons.size() == 2);
		resultPred = builder.buildIsAllocated(
						(SRef)recurse(n.getChildAt(0)), 
						(STime)recurse(n.getChildAt(1)));		
	}
	
	public void visitTEClosedTime(/*@ non_null @*/TEClosedTime n)
	{
		Assert.notFalse(n.sons.size() == 1);
		result = builder.buildEClosedTime((SElems)recurse(n.getChildAt(0)));		
	}
	
	public void visitTFClosedTime(/*@ non_null @*/TFClosedTime n)
	{
		Assert.notFalse(n.sons.size() == 1);
		result = builder.buildFClosedTime((SField)recurse(n.getChildAt(0)));		
	}
	
	public void visitTAsElems(/*@ non_null @*/TAsElems n)
	{
		Assert.notFalse(n.sons.size() == 1);
		result = builder.buildAsElems((SElems)recurse(n.getChildAt(0)));
	}
	
	public void visitTAsField(/*@ non_null @*/TAsField n)
	{
		Assert.notFalse(n.sons.size() == 1);
		//result = builder.buildAsField((SField)recurse(n.getChildAt(0)));
	}
	
	public void visitTAsLockSet(/*@ non_null @*/TAsLockSet n)
	{
		Assert.notFalse(n.sons.size() == 1);
		result = builder.buildAsLockSet((SLockSet)recurse(n.getChildAt(0)));
	}
	
	public void visitTArrayLength(/*@ non_null @*/TArrayLength n)
	{
		Assert.notFalse(n.sons.size() == 1);
		result = builder.buildArrayLength((SArray)recurse(n.getChildAt(0)));
	}
	
	public void visitTArrayFresh(/*@ non_null @*/TArrayFresh n)
	{
		Assert.notFalse(n.sons.size() == 7);
		resultPred = builder.buildArrayFresh(
				(SArray)recurse(n.getChildAt(0)),
				(STime)recurse(n.getChildAt(1)),
				(STime)recurse(n.getChildAt(2)),
				(SElems)recurse(n.getChildAt(3)),
				(SShape)recurse(n.getChildAt(4)),
				(SType)recurse(n.getChildAt(5)),
				(SValue)recurse(n.getChildAt(6))
		);
	}
	
	public void visitTArrayShapeOne(/*@ non_null @*/TArrayShapeOne n)
	{
		Assert.notFalse(n.sons.size() == 1);
		result = builder.buildArrayShapeOne((SInt)recurse(n.getChildAt(0)));
	}
	
	public void visitTArrayShapeMore(/*@ non_null @*/TArrayShapeMore n)
	{
		Assert.notFalse(n.sons.size() == 2);
		result = builder.buildArrayShapeMore(
						(SInt)recurse(n.getChildAt(0)),
						(SShape)recurse(n.getChildAt(1)) );
	}
	
	public void visitTIsNewArray(/*@ non_null @*/TIsNewArray n)
	{
		Assert.notFalse(n.sons.size() == 1);
		resultPred = builder.buildIsNewArray(
						(SArray)recurse(n.getChildAt(0))
						);
	}
	
	public void visitTString(/*@ non_null @*/TString n)
	{
		result = builder.buildString(n.value);
	}
	
	public void visitTBoolean(/*@ non_null @*/TBoolean n)
	{
		result = builder.buildBool(n.value);
	}
	
	public void visitTChar(/*@ non_null @*/TChar n)
	{
		// FIXME is this right?
		result = builder.buildInt((int) n.value);
	}
	
	public void visitTInt(/*@ non_null @*/TInt n)
	{
		result = builder.buildInt(n.value);
	}
	
	public void visitTFloat(/*@ non_null @*/TFloat n) 
	{
		result = builder.buildReal(n.value);		
	}
	
	public void visitTDouble(/*@ non_null @*/TDouble n) 
	{
		result = builder.buildReal(n.value);		
	}
	
	public void visitTNull(/*@ non_null @*/TNull n)
	{
		result = builder.buildNull();
	}
	
	
	public void visitTUnset(/*@non_null*/TUnset n)
	{
		Assert.notFalse(n.sons.size() == 1);
		result = builder.buildUnset(
						(SArray)recurse(n.getChildAt(0)),
						(SInt)recurse(n.getChildAt(1)),
						(SInt)recurse(n.getChildAt(2))
						);
	}
	
	
	public void visitTMethodCall(/*@non_null*/TMethodCall call)
	{
		
	}
	
	
	public void visitTSum(/*@non_null@*/ TSum s)
	{
		// TODO
		Assert.notFalse(false);
	}
	
}
