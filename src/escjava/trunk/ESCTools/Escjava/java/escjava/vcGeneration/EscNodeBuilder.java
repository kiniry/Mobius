package escjava.vcGeneration;

import escjava.ast.TagConstants;
import escjava.vcGeneration.NodeBuilder.Sort;

public abstract class EscNodeBuilder extends NodeBuilder
{
	public interface SShape extends SAny { }
	public interface STime extends SInt { }
	public interface SType extends SAny { }
	public interface SField extends SMap { }
	public interface SElems extends SMap { }
	public interface SLockSet extends SMap { }
	public interface SLock extends SRef { }
	public interface SArray extends SRef { }
	
	final public Sort sortShape = registerSort("shape", sortAny);
	final public Sort sortTime = registerSort("time", sortInt);
	// it seems instances of java.lang.Class are treated as equal to
	// values of sort type...
	final public Sort sortType = sortRef; // registerSort("type", sortAny);
	final public Sort sortLock = sortRef; //registerSort("lock", sortRef);
	final public Sort sortField = sortMap; //registerSort("field", sortMap);
	
	final public Sort sortIntField = registerMapSort(sortRef, sortInt, sortField);
	final public Sort sortRealField = registerMapSort(sortRef, sortReal, sortField);
	final public Sort sortBoolField = registerMapSort(sortRef, sortBool, sortField);
	final public Sort sortRefField = registerMapSort(sortRef, sortRef, sortField);
	
	final public Sort sortOwner = registerMapSort(sortValue, sortRef, sortField);
	
	final public Sort sortArray = sortRef;
	final public Sort sortArrayValue = registerMapSort(sortInt, sortValue);
	final public Sort sortElems = registerMapSort(sortRef, sortArrayValue);
	
	final public Sort sortLockSet = registerMapSort(sortLock, sortBool);
		
	// TODO reflect distinction between Array and ArrayValue in types of functions
	
	// Don't make these final, so deriving class can redefine them
	// if it wishes so. It can also override builder methods.
	
	// Equality
	public PredSymbol symRefEQ = registerPredSymbol("refEQ", new Sort[] { sortRef, sortRef }, TagConstants.REFEQ);
	public PredSymbol symRefNE = registerPredSymbol("refNEQ", new Sort[] { sortRef, sortRef }, TagConstants.REFNE);
	// Built-in orders
	public PredSymbol symAllocLT = registerPredSymbol("<", new Sort[] { sortTime, sortTime }, TagConstants.ALLOCLT);
	public PredSymbol symAllocLE = registerPredSymbol("<=", new Sort[] { sortTime, sortTime }, TagConstants.ALLOCLE);
	public PredSymbol symLockLT = registerPredSymbol("lockLT", new Sort[] { sortLock, sortLock }, TagConstants.LOCKLT);
	public PredSymbol symLockLE = registerPredSymbol("lockLE", new Sort[] { sortLock, sortLock }, TagConstants.LOCKLE);
	public PredSymbol symTypeEQ = registerPredSymbol("typeEQ", new Sort[] { sortType, sortType }, TagConstants.TYPEEQ);
	public PredSymbol symTypeNE = registerPredSymbol("typeNEQ", new Sort[] { sortType, sortType }, TagConstants.TYPENE);
	public PredSymbol symTypeLE = registerPredSymbol("<:", new Sort[] { sortType, sortType }, TagConstants.TYPELE);
	// Dynamic types
	public PredSymbol symIs = registerPredSymbol("is", new Sort[] { sortValue, sortType }, TagConstants.IS);
	public FnSymbol symCast = registerFnSymbol("cast", new Sort[] { sortValue, sortType }, sortValue, TagConstants.CAST);
	public FnSymbol symTypeOf = registerFnSymbol("typeof", new Sort[] { sortValue }, sortType, TagConstants.TYPEOF);	
	// Allocation status
	public PredSymbol symIsAllocated = registerPredSymbol("isAllocated", new Sort[] { sortRef, sortTime }, TagConstants.ISALLOCATED);
	public FnSymbol symEClosedTime = registerFnSymbol("eClosedTime", new Sort[] { sortElems }, sortTime, TagConstants.ECLOSEDTIME);
	public FnSymbol symFClosedTime = registerFnSymbol("fClosedTime", new Sort[] { sortField }, sortTime, TagConstants.FCLOSEDTIME);
	// The as-trick
	public FnSymbol symAsElems = registerFnSymbol("asElems", new Sort[] { sortElems }, sortElems, TagConstants.ASELEMS);
	public FnSymbol symAsField = registerFnSymbol("asField", new Sort[] { sortField, sortType }, sortField, TagConstants.ASFIELD);
	public FnSymbol symAsLockSet = registerFnSymbol("asLockSet", new Sort[] { sortLockSet }, sortLockSet, TagConstants.ASLOCKSET);
	// Arrays
	public FnSymbol symArrayLength = registerFnSymbol("arrayLength", new Sort[] { sortArray }, sortInt, TagConstants.ARRAYLENGTH);
	public FnSymbol symArrayShapeOne = registerFnSymbol("arrayShapeOne", new Sort[] { sortInt }, sortShape, TagConstants.ARRAYSHAPEONE);
	public FnSymbol symArrayShapeMore = registerFnSymbol("arrayShapeMore", new Sort[] { sortInt, sortShape }, sortShape, TagConstants.ARRAYSHAPEMORE);
	public PredSymbol symArrayFresh = registerPredSymbol("arrayFresh", 
			new Sort[] { sortArray, sortTime, sortTime, sortElems, sortShape, sortType, sortValue }, TagConstants.ARRAYFRESH);
	public PredSymbol symIsNewArray = registerPredSymbol("isNewArray", new Sort[] { sortArray }, TagConstants.ISNEWARRAY);
	public FnSymbol symUnset = registerFnSymbol("unset", new Sort[] { sortArrayValue, sortInt, sortInt }, sortArrayValue, TagConstants.UNSET);
	
	// stuff unhandled by the T* interface
	public FnSymbol symArray = registerFnSymbol("array", new Sort[] { sortType }, sortType);

	
	public SPred buildRefEQ(SRef arg1, SRef arg2)
	{
		return buildPredCall(symRefEQ, new SAny[] { arg1, arg2 });
	}
	public SPred buildRefNE(SRef arg1, SRef arg2)
	{
		return buildPredCall(symRefNE, new SAny[] { arg1, arg2 });
	}	
	public SPred buildAllocLT(STime arg1, STime arg2)
	{
		return buildPredCall(symAllocLT, new SAny[] { arg1, arg2 });
	}
	public SPred buildAllocLE(STime arg1, STime arg2)
	{
		return buildPredCall(symAllocLE, new SAny[] { arg1, arg2 });
	}
	public SPred buildLockLE(SLock arg1, SLock arg2)
	{
		return buildPredCall(symLockLE, new SAny[] { arg1, arg2 });
	}
	public SPred buildLockLT(SLock arg1, SLock arg2)
	{
		return buildPredCall(symLockLT, new SAny[] { arg1, arg2 });
	}	
	public SPred buildTypeEQ(SType arg1, SType arg2)
	{
		return buildPredCall(symTypeEQ, new SAny[] { arg1, arg2 });
	}
	public SPred buildTypeNE(SType arg1, SType arg2)
	{
		return buildPredCall(symTypeNE, new SAny[] { arg1, arg2 });
	}
	public SPred buildTypeLE(SType arg1, SType arg2)
	{
		return buildPredCall(symTypeLE, new SAny[] { arg1, arg2 });
	}	
	public SPred buildIs(SValue arg1, SType arg2)
	{
		return buildPredCall(symIs, new SAny[] { arg1, arg2 });
	}
	public SRef buildCast(SValue arg1, SType arg2)
	{
		return (SRef)buildFnCall(symCast, new SAny[] { arg1, arg2 });
	}
	public SType buildTypeOf(SValue arg1)
	{
		return (SType)buildFnCall(symTypeOf, new SAny[] { arg1 });
	}	
	public SPred buildIsAllocated(SRef arg1, STime arg2)
	{
		return buildPredCall(symIsAllocated, new SAny[] { arg1, arg2 });
	}
	public STime buildEClosedTime(SElems arg1)
	{
		return (STime)buildFnCall(symEClosedTime, new SAny[] { arg1 });
	}
	public STime buildFClosedTime(SField arg1)
	{
		return (STime)buildFnCall(symFClosedTime, new SAny[] { arg1 });
	}
	public SElems buildAsElems(SElems arg1)
	{
		return (SElems)buildFnCall(symAsElems, new SAny[] { arg1 });
	}
	public SField buildAsField(SField arg1, SType arg2)
	{
		return (SField)buildFnCall(symAsField, new SAny[] { arg1, arg2 });
	}
	public SLockSet buildAsLockSet(SLockSet arg1)
	{
		return (SLockSet)buildFnCall(symAsLockSet, new SAny[] { arg1 });
	}
	public SPred buildIsNewArray(SArray arg1)
	{
		return buildPredCall(symIsNewArray, new SAny[] { arg1 });
	}
	public SInt buildArrayLength(SArray arg1)
	{
		return (SInt)buildFnCall(symArrayLength, new SAny[] { arg1 });
	}
	public SShape buildArrayShapeOne(SInt arg1)
	{
		return (SShape)buildFnCall(symArrayShapeOne, new SAny[] { arg1 });
	}
	public SShape buildArrayShapeMore(SInt arg1, SShape arg2)
	{
		return (SShape)buildFnCall(symArrayShapeMore, new SAny[] { arg1, arg2 });
	}
	public SPred buildArrayFresh(SArray a, STime alloc1, STime alloc2, SElems elems, SShape shape, SType type, SValue zero)
	{
		return buildPredCall(symArrayFresh, new SAny[] { a, alloc1, alloc2, elems, shape, type, zero });
	}
	public SArray buildUnset(SArray e, SInt low, SInt high)
	{
		return (SArray)buildFnCall(symUnset, new SAny[] { e, low, high });
	}
}
