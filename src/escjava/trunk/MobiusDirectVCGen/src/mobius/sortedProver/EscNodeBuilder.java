package mobius.sortedProver;

import mobius.sortedProver.nodebuilder.members.FnSymbol;
import mobius.sortedProver.nodebuilder.members.PredSymbol;
import mobius.sortedProver.nodebuilder.members.Sort;
import javafe.util.ErrorSet;
import escjava.ast.TagConstants;

/*@ non_null_by_default @*/
public abstract class EscNodeBuilder extends NodeBuilder
{
	final public static Sort sortShape = registerSort("shape", sortAny);
	final public static Sort sortTime = registerSort("time", sortInt);
	// it seems instances of java.lang.Class are treated as equal to
	// values of sort type...
	final public static Sort sortType = sortRef; // registerSort("type", sortAny);
	final public static Sort sortLock = sortRef; //registerSort("lock", sortRef);
	final public static Sort sortField = sortMap; //registerSort("field", sortMap);
	
	final public static Sort sortIntField = registerMapSort(sortRef, sortInt, sortField);
	final public static Sort sortRealField = registerMapSort(sortRef, sortReal, sortField);
	final public static Sort sortBoolField = registerMapSort(sortRef, sortBool, sortField);
	final public static Sort sortRefField = registerMapSort(sortRef, sortRef, sortField);
	
	final public static Sort sortOwner = registerMapSort(sortRef, sortRef, sortField); // RefField
	
	final public static Sort sortArray = sortRef;
	final public static Sort sortArrayValue = registerMapSort(sortInt, sortValue);
	final public static Sort sortElems = registerMapSort(sortRef, sortArrayValue);
	
	final public static Sort sortLockSet = registerMapSort(sortLock, sortBool); // BoolField
		
	// TODO reflect distinction between Array and ArrayValue in types of functions
	
	// Don't make these final, so deriving class can redefine them
	// if it wishes so.
	
	// Equality
	public static PredSymbol symRefEQ = registerPredSymbol("refEQ", new Sort[] { sortRef, sortRef }, TagConstants.REFEQ);
	public static PredSymbol symRefNE = registerPredSymbol("refNEQ", new Sort[] { sortRef, sortRef }, TagConstants.REFNE);
	// Built-in orders
	public static PredSymbol symAllocLT = registerPredSymbol("<", new Sort[] { sortTime, sortTime }, TagConstants.ALLOCLT);
	public static PredSymbol symAllocLE = registerPredSymbol("<=", new Sort[] { sortTime, sortTime }, TagConstants.ALLOCLE);
	public static PredSymbol symLockLT = registerPredSymbol("lockLT", new Sort[] { sortLock, sortLock }, TagConstants.LOCKLT);
	public static PredSymbol symLockLE = registerPredSymbol("lockLE", new Sort[] { sortLock, sortLock }, TagConstants.LOCKLE);
	public static PredSymbol symTypeEQ = registerPredSymbol("typeEQ", new Sort[] { sortType, sortType }, TagConstants.TYPEEQ);
	public static PredSymbol symTypeNE = registerPredSymbol("typeNEQ", new Sort[] { sortType, sortType }, TagConstants.TYPENE);
	public static PredSymbol symTypeLE = registerPredSymbol("<:", new Sort[] { sortType, sortType }, TagConstants.TYPELE);
	// Dynamic types
	public static PredSymbol symIs = registerPredSymbol("is", new Sort[] { sortValue, sortType }, TagConstants.IS);
	public static FnSymbol symCast = registerFnSymbol("cast", new Sort[] { sortValue, sortType }, sortValue, TagConstants.CAST);
	public static FnSymbol symTypeOf = registerFnSymbol("typeof", new Sort[] { sortValue }, sortType, TagConstants.TYPEOF);	
	// Allocation status
	public static PredSymbol symIsAllocated = registerPredSymbol("isAllocated", new Sort[] { sortRef, sortTime }, TagConstants.ISALLOCATED);
	public static FnSymbol symEClosedTime = registerFnSymbol("eClosedTime", new Sort[] { sortElems }, sortTime, TagConstants.ECLOSEDTIME); 
	public static FnSymbol symFClosedTime = registerFnSymbol("fClosedTime", new Sort[] { sortField }, sortTime, TagConstants.FCLOSEDTIME);
	// The as-trick
	public static FnSymbol symAsChild = registerFnSymbol("asChild", new Sort[] { sortType, sortType }, sortType );
	public static FnSymbol symAsElems = registerFnSymbol("asElems", new Sort[] { sortElems }, sortElems, TagConstants.ASELEMS);
	public static FnSymbol symAsField = registerFnSymbol("asField", new Sort[] { sortField, sortType }, sortField, TagConstants.ASFIELD);
	public static FnSymbol symAsLockSet = registerFnSymbol("asLockSet", new Sort[] { sortLockSet }, sortLockSet, TagConstants.ASLOCKSET);
	// Arrays
	public static FnSymbol symArrayLength = registerFnSymbol("arrayLength", new Sort[] { sortArray }, sortInt, TagConstants.ARRAYLENGTH);
	public static FnSymbol symArrayShapeOne = registerFnSymbol("arrayShapeOne", new Sort[] { sortInt }, sortShape, TagConstants.ARRAYSHAPEONE);
	public static FnSymbol symArrayShapeMore = registerFnSymbol("arrayShapeMore", new Sort[] { sortInt, sortShape }, sortShape, TagConstants.ARRAYSHAPEMORE);
	public static PredSymbol symArrayFresh = registerPredSymbol("arrayFresh", 
			new Sort[] { sortArray, sortTime, sortTime, sortElems, sortShape, sortType, sortValue }, TagConstants.ARRAYFRESH);
	public static PredSymbol symIsNewArray = registerPredSymbol("isNewArray", new Sort[] { sortArray }, TagConstants.ISNEWARRAY);
	public static FnSymbol symUnset = registerFnSymbol("unset", new Sort[] { sortArrayValue, sortInt, sortInt }, sortArrayValue, TagConstants.UNSET);
	
	// stuff unhandled by the T* interface
	public static FnSymbol symArray = registerFnSymbol("_array", new Sort[] { sortType }, sortType);	
    public static FnSymbol symIntern = registerFnSymbol("|intern:|", new Sort[] { sortInt, sortInt }, sortString, TagConstants.INTERN);
    public static PredSymbol symInterned = registerPredSymbol("|interned:|", new Sort[] { sortString }, TagConstants.INTERNED);
    public static FnSymbol symStringCat = registerFnSymbol("stringCat", new Sort[] { sortString, sortString, sortTime }, sortString, TagConstants.STRINGCAT);
    // the 3rd argument seems to be sometimes int and sometimes string
    public static PredSymbol symStringCatP = registerPredSymbol("stringCatP", new Sort[] { sortString, sortString, sortValue, sortTime, sortTime }, TagConstants.STRINGCATP);
    public static PredSymbol symNonNullElems = registerPredSymbol("nonnullelements", new Sort[] { sortArray, sortElems }, TagConstants.ELEMSNONNULL);
    public static FnSymbol symElemType = registerFnSymbol("elemtype", new Sort[] { sortType }, sortType, TagConstants.ELEMTYPE);
    public static FnSymbol symMax = registerFnSymbol("max", new Sort[] { sortLockSet }, sortLock, TagConstants.MAX);
    public static FnSymbol symArrayMake = registerFnSymbol("arrayMake", new Sort[] { sortTime, sortTime, sortShape, sortType, sortValue }, sortArray, TagConstants.ARRAYMAKE);
    public static FnSymbol symClassLiteral = registerFnSymbol("classLiteral", new Sort[] { sortType }, sortRef, TagConstants.CLASSLITERALFUNC);


    public static /*@ nullable @*/FnSymbol mapFnSymbolTo(EscNodeBuilder other, FnSymbol sym)
    {
    	if (sym == symRefEQ) return other.symRefEQ;
    	else if (sym == symRefNE) return other.symRefNE;
    	else if (sym == symAllocLT) return other.symAllocLT;
    	else if (sym == symAllocLE) return other.symAllocLE;
    	else if (sym == symLockLT) return other.symLockLT;
    	else if (sym == symLockLE) return other.symLockLE;
    	else if (sym == symTypeEQ) return other.symTypeEQ;
    	else if (sym == symTypeNE) return other.symTypeNE;
    	else if (sym == symTypeLE) return other.symTypeLE;
    	else if (sym == symIs) return other.symIs;
    	else if (sym == symCast) return other.symCast;
    	else if (sym == symTypeOf) return other.symTypeOf;
    	else if (sym == symIsAllocated) return other.symIsAllocated;
    	else if (sym == symEClosedTime) return other.symEClosedTime;
    	else if (sym == symFClosedTime) return other.symFClosedTime;
    	else if (sym == symAsElems) return other.symAsElems;
    	else if (sym == symAsField) return other.symAsField;
    	else if (sym == symAsLockSet) return other.symAsLockSet;
    	else if (sym == symArrayLength) return other.symArrayLength;
    	else if (sym == symArrayShapeOne) return other.symArrayShapeOne;
    	else if (sym == symArrayShapeMore) return other.symArrayShapeMore;
    	else if (sym == symArrayFresh) return other.symArrayFresh;
    	else if (sym == symIsNewArray) return other.symIsNewArray;
    	else if (sym == symUnset) return other.symUnset;
    	else if (sym == symArray) return other.symArray;
    	else if (sym == symIntern) return other.symIntern;
    	else if (sym == symInterned) return other.symInterned;
    	else if (sym == symStringCat) return other.symStringCat;
    	else if (sym == symStringCatP) return other.symStringCatP;
    	else if (sym == symNonNullElems) return other.symNonNullElems;
    	else if (sym == symElemType) return other.symElemType;
    	else if (sym == symMax) return other.symMax;
    	else if (sym == symArrayMake) return other.symArrayMake;
    	else if (sym == symClassLiteral) return other.symClassLiteral;
    	//ErrorSet.fatal("cannot map " + sym + " from " + this + " to " + other);
    	return null;
    }
    
    public static Sort canonicalizeSort(Sort s)
    {
    	s = s.theRealThing();
    	Sort from = s.getMapFrom();
    	if (from != null) from = from.theRealThing();
    	if (from == null) {
    		return s;
    	} else if (from == sortRef) {
    		Sort to = s.getMapFrom().theRealThing();
    		if (to == sortRef) return sortRefField;
    		if (to == sortInt) return sortIntField;
    		if (to == sortBool) return sortBoolField;
    		if (to == sortReal) return sortRealField;
    		to = canonicalizeSort(to);
    		if (to == sortArrayValue) return sortElems;
    		return s;
    	} else if (from == sortInt) {
    		Sort to = s.getMapFrom().theRealThing();
    		if (to == sortValue) return sortArrayValue;
    		return s;
    	} else {
    		return s;
    	}
    }

	public static Sort mapSortTo(EscNodeBuilder other, Sort sort)
	{
		sort = canonicalizeSort(sort);
		if (sort == sortIntField) return other.sortIntField;
		else if (sort == sortRealField) return other.sortRealField;
		else if (sort == sortBoolField) return other.sortBoolField;
		else if (sort == sortRefField) return other.sortRefField;
		else if (sort == sortArrayValue) return other.sortArrayValue;
		else if (sort == sortElems) return other.sortElems;
		else if (sort == sortShape) return other.sortShape;
		else if (sort == sortTime) return other.sortTime;
		else if (sort == sortPred) return other.sortPred;
		else if (sort == sortAny) return other.sortAny;
		else if (sort == sortValue) return other.sortValue;
		else if (sort == sortBool) return other.sortBool;
		else if (sort == sortInt) return other.sortInt;
		else if (sort == sortReal) return other.sortReal;
		else if (sort == sortRef) return other.sortRef;
		else if (sort == sortMap) return other.sortMap;
		ErrorSet.fatal("cannot map " + sort + " from " + //this +
				" to " + other);
		return null;
	}
}
