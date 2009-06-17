package escjava.sortedProver.cvc3;

//import java.lang.reflect.Method;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;

import javafe.util.Assert;
import javafe.util.ErrorSet;
import javafe.util.Info;

import escjava.ast.TagConstants;
import escjava.sortedProver.EscNodeBuilder;
import escjava.sortedProver.Lifter;

import cvc3.*;


/*@ non_null_by_default @*/
public class Cvc3NodeBuilder extends EscNodeBuilder {

    //
    /// debug
    //
    final static private boolean printQuery = false;


    boolean optMultiTriggers = true;
    boolean optManualTriggers = true;
    public boolean optNonnullelements = true;
    public boolean optIsallocated = false;
    public boolean optBuiltinTrans = true;

    //
    /// debug
    //
    // can't use cvc3's preprocessing, as it might remove expressions
    // which we need for label relevance analysis.
    //
    // tried to use some rewriting here, but:
    // - wasn't effective in terms of performance gain
    // - label propagation during simplification is tricky,
    //   and the current code doesn't get it quite right.
    //   that is, some relevant labels might be lost,
    //   and thus counterexamples may be missed.
    // rewrite using simple rules
    final static private boolean rewrite = false;
    // rewrite using cvc3's state
    final static private boolean rewriteCvc3 = false;


    // the cvc instance
    final private cvc3.ValidityChecker prover;

    final private Cvc3Prover cvcProver;


    //
    // sorts
    //

    // for internal errors
    final public Type typeError;

    // the cvc types mirroring the sorts used by EscJava / NodeBuilder
    final public Type typePred;
    final public Type typeValue;
    final public Type typeBool;
    final public Type typeInt;
    final public Type typeReal;
    final public Type typeRef;
    final public Type typeString;

    final public Type typeShape;
    final public Type typeTime;
    final public Type typeType;
    final public Type typeLock;

    final public Type typeField;
    final public Type typeBoolField;
    final public Type typeIntField;
    final public Type typeRealField;
    final public Type typeRefField;
    final public Type typeArray;
    final public Type typeElems;
    final public Type typeLockSet;


    // predefined cvc operators

    // casting between cvc types
    final public Op refToType;
    final public Op typeToRef;

    final public Op valueToBool;
    final public Op valueToInt;
    final public Op valueToReal;
    final public Op valueToRef;
    final public Op boolToValue;
    final public Op intToValue;
    final public Op realToValue;
    final public Op refToValue;
    /*
    final public Op fieldToBoolField;
    final public Op fieldToIntField;
    final public Op fieldToRealField;
    final public Op fieldToRefField;
    final public Op boolFieldToField;
    final public Op intFieldToField;
    final public Op realFieldToField;
    final public Op refFieldToField;
    */
    final public Op[] casts;

    // field mapping functions specialized for the field instances
    final public Op asFieldBool;
    final public Op asFieldInt;
    final public Op asFieldReal;
    final public Op asFieldRef;
    /*
    final public Op fClosedTimeBool;
    final public Op fClosedTimeInt;
    final public Op fClosedTimeReal;
    final public Op fClosedTimeRef;
    */

    // predefined EscJava expressions
    final public Cvc3Ref escNull;
    final public Cvc3Pred escTrue;
    final public Cvc3Pred escFalse;
    final public Cvc3Bool escBTrue;
    final public Cvc3Bool escBFalse;


    // EscJava symbols, that for some reason are not defined in EscNodeBuilder
    // types
    public FnSymbol getTypeSymbol(int tag) {
	return registerConstant(escjava.ast.TagConstants.toString(tag), sortType);
    }

    final public FnSymbol symTArray = getTypeSymbol(TagConstants.ARRAYTYPE);
    final public FnSymbol symTBoolean = getTypeSymbol(TagConstants.BOOLEANTYPE);
    final public FnSymbol symTChar = getTypeSymbol(TagConstants.CHARTYPE);
    final public FnSymbol symTByte = getTypeSymbol(TagConstants.BYTETYPE);
    final public FnSymbol symTShort = getTypeSymbol(TagConstants.SHORTTYPE);
    final public FnSymbol symTInt = getTypeSymbol(TagConstants.INTTYPE);
    final public FnSymbol symTLong = getTypeSymbol(TagConstants.LONGTYPE);
    final public FnSymbol symTFloat = getTypeSymbol(TagConstants.FLOATTYPE);
    final public FnSymbol symTDouble = getTypeSymbol(TagConstants.DOUBLETYPE);
    final public FnSymbol symTBigInt = getTypeSymbol(TagConstants.BIGINTTYPE);
    //:TODO: final public FnSymbol symTReal = getTypeSymbol(TagConstants.REALTYPE);
    final public FnSymbol symTVoid = getTypeSymbol(TagConstants.VOIDTYPE);
    //???FnSymbol symTType = getTypeSymbol(TagConstants.TYPE);
    // special values
    //:TODO: not as hard-coded string - but how?
    final public FnSymbol symTObject = registerConstant("T_java.lang.Object", sortType);
    final public FnSymbol symTClass = registerConstant("T_java.lang.Class", sortType);
    final public FnSymbol symTCloneable = registerConstant("T_java.lang.Cloneable", sortType);
    final public FnSymbol symTString = registerConstant("T_java.lang.String", sortType);
    final public FnSymbol symAlloc = registerConstant("alloc", sortTime);
    final public FnSymbol symvAllocTime = registerFnSymbol(escjava.ast.TagConstants.toString(TagConstants.VALLOCTIME),
							   new Sort[] { sortRef }, sortTime, TagConstants.VALLOCTIME);

    final public FnSymbol symIntegralDIV = registerFnSymbol(escjava.ast.TagConstants.toString(TagConstants.INTEGRALDIV),
							    new Sort[] { sortInt, sortInt }, sortInt,
							    TagConstants.INTEGRALDIV);
    final public FnSymbol symIntegralMOD = registerFnSymbol(escjava.ast.TagConstants.toString(TagConstants.INTEGRALMOD),
							    new Sort[] { sortInt, sortInt }, sortInt,
							    TagConstants.INTEGRALMOD);
    final public FnSymbol symFloatingDIV = registerFnSymbol(escjava.ast.TagConstants.toString(TagConstants.FLOATINGDIV),
							    new Sort[] { sortInt, sortInt }, sortInt,
							    TagConstants.FLOATINGDIV);
    final public FnSymbol symFloatingMOD = registerFnSymbol(escjava.ast.TagConstants.toString(TagConstants.FLOATINGMOD),
							    new Sort[] { sortInt, sortInt }, sortInt,
							    TagConstants.FLOATINGMOD);

    //
    // registries / mappings (for memoization)
    //

    // EscJava sort -> cvc type
    final private HashMap typeMap = new HashMap();

    // EscJava symbol -> cvc constant/operator
    final private HashMap symbolMap = new HashMap();

    // EscJava QuantVar -> cvc bound var
    final private HashMap varsMap = new HashMap();

    // cvc expr <-> EscJava node (STerm, SValue, SRef, ...)
    // 
    final private HashMap escMap = new HashMap();


    //
    // methods
    //


    public Cvc3NodeBuilder(cvc3.ValidityChecker prover, Cvc3Prover cvcProver,
                           boolean multiTriggers, boolean manualTriggers,
                           boolean nonnullelements, boolean isallocated, boolean builtinTrans)
	throws cvc3.Cvc3Exception {

	this.prover = prover;
	this.cvcProver = cvcProver;
	this.optMultiTriggers = multiTriggers;
        this.optNonnullelements = nonnullelements;
        this.optIsallocated = isallocated;
        this.optBuiltinTrans = builtinTrans;
	this.optManualTriggers = manualTriggers;

	// sorts
	typeError = prover.createType("error");
	typePred = prover.boolType();
	typeValue = prover.createType("Value");
	typeBool = prover.bitvecType(1);
	typeInt = prover.intType();
	typeReal = prover.realType();
	typeRef = prover.createType("Ref");
	typeString = typeRef;
	
	typeShape = prover.createType("Shape");
	typeTime = typeInt;
	typeType = prover.createType("JavaType");
	typeLock = typeRef;

	typeField = prover.createType("Field");
	//typeField = prover.arrayType(typeValue, typeValue);
	typeBoolField = prover.arrayType(typeRef, typeBool);
	typeIntField = prover.arrayType(typeRef, typeInt);
	typeRealField = prover.arrayType(typeRef, typeReal);
	typeRefField = prover.arrayType(typeRef, typeRef);

	typeArray = prover.arrayType(typeInt, typeValue);
	typeElems = prover.arrayType(typeRef, typeArray);
	typeLockSet = prover.arrayType(typeLock, typeBool);
	
	// operators
	//	intToReal = prover.createOp("intToReal", prover.funType(typeInt, typeReal));
	//	realToInt = prover.createOp("realToInt", prover.funType(typeReal, typeInt));

	refToType = prover.createOp("refToType", prover.funType(typeRef, typeType));
	typeToRef = prover.createOp("typeToRef", prover.funType(typeType, typeRef));

	valueToBool = prover.createOp("valueToBool", prover.funType(typeValue, typeBool));  
	valueToInt = prover.createOp("valueToInt", prover.funType(typeValue, typeInt));
	valueToReal = prover.createOp("valueToReal", prover.funType(typeValue, typeReal));
	valueToRef = prover.createOp("valueToRef", prover.funType(typeValue, typeRef));
	boolToValue = prover.createOp("boolToValue", prover.funType(typeBool, typeValue));  
	intToValue = prover.createOp("intToValue", prover.funType(typeInt, typeValue));  
	realToValue = prover.createOp("realToValue", prover.funType(typeReal, typeValue));  
	refToValue = prover.createOp("refToValue", prover.funType(typeRef, typeValue));  
	/*
	fieldToBoolField = prover.createOp("fieldToBoolField", prover.funType(typeField, typeBoolField));
	fieldToIntField = prover.createOp("fieldToIntField", prover.funType(typeField, typeIntField));
	fieldToRealField = prover.createOp("fieldToRealField", prover.funType(typeField, typeRealField));
	fieldToRefField = prover.createOp("fieldToRefField", prover.funType(typeField, typeRefField));
	boolFieldToField = prover.createOp("boolFieldToField", prover.funType(typeBoolField, typeField));
	intFieldToField = prover.createOp("intFieldToField", prover.funType(typeIntField, typeField));
	realFieldToField = prover.createOp("realFieldToField", prover.funType(typeRealField, typeField));
	refFieldToField = prover.createOp("refFieldToField", prover.funType(typeRefField, typeField));
	*/
	asFieldBool = prover.createOp("asFieldBool",
	  prover.funType(Arrays.asList (new Type[] { typeBoolField, typeType }), typeBoolField));
	asFieldInt = prover.createOp("asFieldInt",
	  prover.funType(Arrays.asList (new Type[] { typeIntField, typeType }), typeIntField));
	asFieldReal = prover.createOp("asFieldReal",
	  prover.funType(Arrays.asList (new Type[] { typeRealField, typeType }), typeRealField));
	asFieldRef = prover.createOp("asFieldRef",
	  prover.funType(Arrays.asList (new Type[] { typeRefField, typeType }), typeRefField));
	/*	fClosedTimeBool = prover.createOp("fClosedTimeBool", prover.funType(typeBoolField, typeTime));
	fClosedTimeInt = prover.createOp("fClosedTimeInt", prover.funType(typeIntField, typeTime));
	fClosedTimeReal = prover.createOp("fClosedTimeReal", prover.funType(typeRealField, typeTime));
	fClosedTimeRef = prover.createOp("fClosedTimeRef", prover.funType(typeRefField, typeTime));
	*/
	casts = new Op[] {
	    refToType, typeToRef,
	    valueToBool, valueToInt, valueToReal, valueToRef,
	    boolToValue, intToValue, realToValue, refToValue//,
	    //fieldToBoolField, fieldToIntField, fieldToRealField, fieldToRefField,
	    //boolFieldToField, intFieldToField, realFieldToField, refFieldToField
	};
	
	// expressions
	escNull = new Cvc3Ref(prover.varExpr("null", typeRef));
	escTrue = new Cvc3Pred(prover.trueExpr());
	escFalse = new Cvc3Pred(prover.falseExpr());
	escBTrue = new Cvc3Bool(prover.newBVConstExpr("1"));
	escBFalse = new Cvc3Bool(prover.newBVConstExpr("0"));
    }

    public void setup() throws cvc3.Cvc3Exception {
	setupTypes();
	setupSymbols();
    }


    // mapping: escjava sorts -> cvc types
    protected void setupTypes() {
	typeMap.put(sortPred.name, typePred);
	typeMap.put(sortValue.name, typeValue);
	typeMap.put(sortBool.name, typeBool);
	typeMap.put(sortInt.name, typeInt);
	typeMap.put(sortReal.name, typeReal);
	typeMap.put(sortRef.name, typeRef);
	typeMap.put(sortString.name, typeString);

	typeMap.put(sortShape.name, typeShape);
	typeMap.put(sortTime.name, typeTime);
	typeMap.put(sortType.name, typeType);
	typeMap.put(sortLock.name, typeLock);

	typeMap.put(sortField.name, typeField);
	typeMap.put(sortIntField.name, typeIntField);
	typeMap.put(sortRealField.name, typeRealField);
	typeMap.put(sortBoolField.name, typeBoolField);
	typeMap.put(sortOwner.name, typeRefField);

	typeMap.put(sortArrayValue.name, typeArray);
	typeMap.put(sortElems.name, typeElems);
	typeMap.put(sortLockSet.name, typeLockSet);
    }

    // x2y(y2x(y)) = y
    //
    // adding y2x(x2y(x)) = x as well is unsound,
    // as then we don't have embeddings of int/real/bool/ref into value,
    // but bijections, which also make int and bool isomorphic
    protected void setupCast(Op x2y, Op y2x, Expr x, Expr y) throws cvc3.Cvc3Exception {
	if (printQuery) System.out.println("%% Cvc3NodeBuilder.setupCast:");

	List vars = Arrays.asList(new Expr[] { y } );
	Expr eq = prover.eqExpr(prover.funExpr(x2y, prover.funExpr(y2x, y)), y);
	List triggers = new ArrayList();
	List trigger1 = new ArrayList();
	trigger1.add(prover.funExpr(y2x, y));
	triggers.add(prover.listExpr(trigger1));

	Expr p = prover.forallExpr(vars, eq, triggers);

	if (printQuery) {
	    System.out.println("ASSERT (" + p.toString() + ");");
	}
	cvcProver.declareAxiom(new Cvc3Pred(p));
    }

    // setup casting embeddings between types,
    // i.e. between value, the super type,
    // and its subtypes bool/int/real/ref,
    // and also between type and ref for some reflection vcs
    protected void setupCast() throws cvc3.Cvc3Exception {
	/*
	Expr vt = prover.varExpr("t", typeType);
	Expr vv = prover.varExpr("v", typeValue);
	Expr vb = prover.varExpr("b", typeBool);
	Expr vi = prover.varExpr("i", typeInt);
	Expr vr = prover.varExpr("r", typeReal);
	Expr vref = prover.varExpr("ref", typeRef);
	Expr vf = prover.varExpr("f", typeField);
	Expr vfb = prover.varExpr("fb", typeBoolField);
	Expr vfi = prover.varExpr("fi", typeIntField);
	Expr vfr = prover.varExpr("fr", typeRealField);
	Expr vfref = prover.varExpr("fref", typeRefField);
	*/
	Expr vt = prover.boundVarExpr("t", "t_" + typeType.toString(), typeType);
	Expr vv = prover.boundVarExpr("v", "v_" + typeValue.toString(), typeValue);
	Expr vb = prover.boundVarExpr("b", "b_" + typeBool.toString(), typeBool);
	Expr vi = prover.boundVarExpr("i", "i_" + typeInt.toString(), typeInt);
	Expr vr = prover.boundVarExpr("r", "r_" + typeReal.toString(), typeReal);
	Expr vref = prover.boundVarExpr("ref", "ref_" + typeRef.toString(), typeRef);
	/*
	Expr vf = prover.boundVarExpr("f", "f_" + typeField.toString(), typeField);
	Expr vfb = prover.boundVarExpr("fb", "fb_" + typeBoolField.toString(), typeBoolField);
	Expr vfi = prover.boundVarExpr("fi", "fi_" + typeIntField.toString(), typeIntField);
	Expr vfr = prover.boundVarExpr("fr", "fr_" + typeRealField.toString(), typeRealField);
	Expr vfref = prover.boundVarExpr("fref", "fref_" + typeRefField.toString(), typeRefField);
	*/
	setupCast(refToType, typeToRef, vref, vt);

	setupCast(valueToBool, boolToValue, vv, vb);
	setupCast(valueToInt, intToValue, vv, vi);
	setupCast(valueToReal, realToValue, vv, vr);
	setupCast(valueToRef, refToValue, vv, vref);
	/*
	setupCast(fieldToBoolField, boolFieldToField, vf, vfb);
	setupCast(fieldToIntField, intFieldToField, vf, vfi);
	setupCast(fieldToRealField, realFieldToField, vf, vfr);
	setupCast(fieldToRefField, refFieldToField, vf, vfref);
	*/
    }

    // special predefined symbols
    protected void setupSymbols() throws cvc3.Cvc3Exception {
	setupCast();

	// make sure that fCloseTime is applied to ref fields only,
	// not general fields, to avoid casting
	String nameFClosedTime = uniqueName(symFClosedTime);
	symbolMap.put(nameFClosedTime,
	  prover.createOp(nameFClosedTime, prover.funType(typeRefField, typeTime)));
    }


    // escjava might use the same name with different types
    // in different queries using one prover instance
    // as cvc can't handle this, make the names unique by encoding their type
    public String uniqueName(FnSymbol fn) {
	StringBuffer name = new StringBuffer(fn.name + ":");
	for (int i = 0; i < fn.argumentTypes.length; ++i) {
	    name.append("_" + fn.argumentTypes[i]);
	}
	name.append("_" + fn.retType);

	return toCvc3Input(name.toString());
	//return name.toString();
    }

    // :TODO: make readable as cvc textual input (helpful for debugging)
    public String toCvc3Input(String string) {
	String cvcSuitable = string;

	// :TODO: check if stuff we omitted when translating the background predicate
	// does actually occur in a test
	assert(!string.equals("intFirst"));
	assert(!string.equals("intLast"));
	assert(!string.equals("longFirst"));
	assert(!string.equals("longLast"));
	assert(!string.equals("arrayMake"));
	assert(!string.equals("arrayType"));
	assert(!string.equals("isNewArray"));
	// :TODO: test495 StackCheck.java
        assert(!string.equals("unset"));
	assert(!string.equals("stringCat"));
	assert(!string.equals("stringCatP"));
	assert(!string.equals("next"));
	assert(!string.equals("integralEQ"));
	assert(!string.equals("integralLE"));
	assert(!string.equals("integralLT"));
	assert(!string.equals("integralGE"));
	assert(!string.equals("integralGT"));
	assert(!string.equals("integralNE"));
	assert(!string.equals("integralAnd"));
	assert(!string.equals("integralOr"));
	assert(!string.equals("integralDiv"));
	assert(!string.equals("integralXor"));
	assert(!string.equals("integralMod"));
	assert(!string.equals("intShiftL"));
	assert(!string.equals("longShiftL"));
	assert(!string.equals("floatingEQ"));
	assert(!string.equals("floatingLE"));
	assert(!string.equals("floatingLT"));
	assert(!string.equals("floatingGE"));
	assert(!string.equals("floatingGT"));
	assert(!string.equals("floatingNE"));
	assert(!string.equals("floatingADD"));
	assert(!string.equals("floatingMUL"));
	assert(!string.equals("floatingMOD"));
	assert(!string.equals("refEQ"));
	assert(!string.equals("refNE"));

        // strictly speaking should first replace _ by __
	// to avoid non-unique renaming

	// not really sure what to do with unknown tags:
 	// "Unknown ESC tag _LT_251 (+56) _GT___type"
	// it's probably an error in the sorted translation.
        cvcSuitable = cvcSuitable.replaceAll(" ", "_");
        cvcSuitable = cvcSuitable.replaceAll("\\+", "_PL_");
        cvcSuitable = cvcSuitable.replaceAll("\\(", "_LP_");
        cvcSuitable = cvcSuitable.replaceAll("\\)", "_RP_");
        cvcSuitable = cvcSuitable.replaceAll("<:", "typeLE");
        cvcSuitable = cvcSuitable.replaceAll(":", "_");
        cvcSuitable = cvcSuitable.replaceAll(",", "_C_");
        cvcSuitable = cvcSuitable.replaceAll("=", "_EG_");
        cvcSuitable = cvcSuitable.replaceAll("<", "_LT_");
        cvcSuitable = cvcSuitable.replaceAll(">", "_GT_");
        cvcSuitable = cvcSuitable.replaceAll("@", "_AT_");
        cvcSuitable = cvcSuitable.replaceAll("#", "_SH_");
        cvcSuitable = cvcSuitable.replaceAll("!", "_EX_");
        cvcSuitable = cvcSuitable.replaceAll("%", "_PR_");
        cvcSuitable = cvcSuitable.replaceAll("-", "_MI_");
        cvcSuitable = cvcSuitable.replaceAll("\\|", "_PI_");
        cvcSuitable = cvcSuitable.replaceAll("\\.", "_D_");
        cvcSuitable = cvcSuitable.replaceAll("\\[", "_LB_");
        cvcSuitable = cvcSuitable.replaceAll("\\]", "_RB_");

        return cvcSuitable;
    }


    //
    // Mapping: Sort -> Type
    //

    // mapping of a basic sort (not function or predicate) to its cvc type
    protected Type mapValSort(Sort sort) throws Cvc3Exception {
	Cvc3Prover.print("mapValSort: " + sort);
	if (typeMap.containsKey(sort.name)) {
	    return (Type) typeMap.get(sort.name);
	} else if (sort.isSubSortOf(sortMap)) {
	    Sort fromSort = sort.getMapFrom();
	    Sort toSort = sort.getMapTo();
	    assert(fromSort != null);
	    assert(toSort != null);
	    Type type = prover.arrayType(mapValSort(fromSort), mapValSort(toSort));
	    typeMap.put(sort.name, type);
	    return type;
	} else {
	    ErrorSet.fatal("mapValSort");
	    assert(false);
	    return prover.createType("UnknownType");
	}
    }

    // mapping of a function symbol to its cvc type
    protected Type mapFunSort(FnSymbol symbol) throws Cvc3Exception {
	Cvc3Prover.print("mapFunSort: " + symbol);
	if (typeMap.containsKey(symbol.name)) {
	    return (Type) typeMap.get(symbol.name);
	} else {
	    List argumentTypes = new ArrayList();
	    for (int i = 0; i < symbol.argumentTypes.length; ++i) {
		argumentTypes.add(mapValSort(symbol.argumentTypes[i]));
	    }
	    Type returnType = mapValSort(symbol.retType);
	    Type type = prover.funType(argumentTypes, returnType);
	    typeMap.put(symbol.name, type);
	    return type;
	}
    }

    // mapping of a predicate symbol to its cvc type
    protected Type mapPredSort(PredSymbol symbol) throws Cvc3Exception {
	return mapFunSort(symbol);
    }



    //
    // Mapping: Symbol -> Constant/Operator
    //

    // mapping of a constant symbol to its cvc constant expression
    protected Expr mapValSymbol(FnSymbol symbol) throws Cvc3Exception {
	Cvc3Prover.print("mapValSymbol: " + symbol.name);
	assert(symbol.argumentTypes.length == 0);
	String name = uniqueName(symbol);
	if (symbolMap.containsKey(name)) {
	    return (Expr) symbolMap.get(name);
	} else {
	    Expr var = prover.varExpr(name, mapValSort(symbol.retType));
	    symbolMap.put(name, var);
	    return var;
	}
    }

    // mapping of a function symbol to its cvc operator
    protected Op mapFunSymbol(FnSymbol symbol) throws Cvc3Exception {
	Cvc3Prover.print("mapFunSymbol: " + symbol.name);
	String name = uniqueName(symbol);
	if (symbolMap.containsKey(name)) {
	    return (Op) symbolMap.get(name);
	} else {
	    Op op = prover.createOp(name, mapFunSort(symbol));
            
            // special treatment for builtin transitivity
            if (optBuiltinTrans && symbol == symTypeLE) {
                op = prover.transClosure(op);
            }

	    symbolMap.put(name, op);
	    return op;
	}
    }

    // mapping of a predicate symbol to its cvc operator
    protected Op mapPredSymbol(PredSymbol symbol) throws Cvc3Exception {
	return mapFunSymbol(symbol);
    }


    //
    // Mapping: Bound Variables
    //

    // mapping of a bound variable to its cvc bound variable
    protected Cvc3Any getBoundVarExpr(QuantVar bvar) {
	String key = bvar.name + ":" + bvar.type;
	if (varsMap.containsKey(key)) {
	    return (Cvc3Any) varsMap.get(key);
	} else {
	    try {
		Expr e = prover.boundVarExpr(toCvc3Input(bvar.name),
					     toCvc3Input(bvar.name + bvar.type.toString()),
					     mapValSort(bvar.type));
		Cvc3Any var = (Cvc3Any) wrapExpr(e);
		//Cvc3Any var = wrapAnyExpr(e, bvar.type);
		varsMap.put(key, var);
		return var;
	    } catch (cvc3.Cvc3Exception e) {
		ErrorSet.fatal(e.toString());
		throw new Error(e);
	    }
	}
    }


    // cvc predicates for memoization, with rewriting for atoms
    public Cvc3Pred registerCvc3Pred(Object key, Cvc3Pred p) throws Cvc3Exception {
	Expr e = p.getExpr();
	assert(e.getType().equals(prover.boolType()));
	assert(!(p instanceof Cvc3Label)); // should not register labels
	if (rewriteCvc3 && e.isPropAtom()) {
	    if (prover.simplify(e).equals(prover.trueExpr())) {
		Cvc3Pred node = transferLabels(p, (Cvc3Pred) buildTrue());
		assert(!escMap.containsKey(key));
		escMap.put(key, node);
		assert(escMap.containsKey(key));
		return node;
	    } else if (prover.simplify(e).equals(prover.falseExpr())) {
		Cvc3Pred node = transferLabels(p, (Cvc3Pred) buildFalse());
		assert(!escMap.containsKey(key));
		escMap.put(key, node);
		return node;
	    }
	}
	// no simplification
	escMap.put(key, p);
	return p;
    }


    //
    // type conversions
    //

    // find common subtype of t1 and t2,
    // assuming that one is an instance of the other.
    public Type unify(Type t1, Type t2) {
	if (t1.equals(t2)) {
	    return t1;
	}

	// int to real
	else if (t1.equals(typeInt) && t2.equals(typeReal)) {
	    return typeReal;
	} else if (t1.equals(typeReal) && t2.equals(typeInt)) {
	    return typeReal;
	}

	// value to bool/int/real/ref
	else if (t1.equals(typeValue)) {
	    if (t2.equals(typeBool)
		|| 
		t2.equals(typeInt)
		||
		t2.equals(typeReal)
		||
		t2.equals(typeRef)) {
		return t2;
	    }
	}
	else if (t2.equals(typeValue)) {
	    if (t1.equals(typeBool)
		|| 
		t1.equals(typeInt)
		||
		t1.equals(typeReal)
		||
		t1.equals(typeRef)) {
		return t1;
	    }
	}

	// fields to field instances
	else if (t1.equals(typeField)) {
	    if (t2.equals(typeBoolField)
		||
		t2.equals(typeIntField)
		||
		t2.equals(typeRealField)
		||
		t2.equals(typeRefField)) {
		return t2;
	    }
	}
	else if (t2.equals(typeField)) {
	    if (t1.equals(typeBoolField)
		||
		t1.equals(typeIntField)
		||
		t1.equals(typeRealField)
		||
		t1.equals(typeRefField)) {
		return t1;
	    }
	}

	ErrorSet.fatal("unify: " + t1 + " <---> " + t2);
	assert(false);
	return typeError;
    }


    //
    // cast an expression to the given type
    //

    public boolean isArithType(Expr expr) throws Cvc3Exception {
	Type t = expr.getChild(0).getType();
	return t.equals(typeInt) || t.equals(typeReal);
    }

    public boolean isCastOp(Op op) {
	for (int i = 0; i < casts.length; ++i) {
	    if (casts[i].equals(op)) {
		return true;
	    }
	}
	return false;
    }

    // expr should be cast to cast(expr),
    // but if expr has the form inverse(expr),
    // with inverse the inverse of case,
    // then cast(inverse(expr)) simplifies to expr
    public Expr simplifyCast(Expr expr, Op cast, Op inverse, Op inverse2) throws Cvc3Exception {
	if (expr.isApply()
	    &&
	    (expr.getOp().equals(inverse) || expr.getOp().equals(inverse2))) {
	    assert(expr.arity() == 1);
	    return expr.getChild(0);
	} else {
	    return prover.funExpr(cast, expr);
	}
    }

    public Expr simplifyCast(Expr expr, Op cast, Op inverse) throws Cvc3Exception {
	return simplifyCast(expr, cast, inverse, null);
    }

    public boolean sameCast(Expr expr1, Expr expr2) throws Cvc3Exception {
	if (expr1.isApply() && expr2.isApply()) {
	    Op op1 = expr1.getOp();
	    Op op2 = expr2.getOp();
	    if (op1.equals(op2) && isCastOp(op1) && isCastOp(op2)) {
		assert(expr1.arity() == 1);
		assert(expr2.arity() == 1);
		return true;
	    }
	}

	return false;
    }


    public Expr cast(Expr expr, Sort sort) throws Cvc3Exception {
	return cast(expr, mapValSort(sort));
    }

    public Expr cast(Expr expr, Type type) throws Cvc3Exception {
	Cvc3Prover.print("cast: " + expr + " <---> " + type);
	Type eType = expr.getType();
	if (eType.equals(type)) {
	    return expr;
	}

	// real <-> int
	// :TODO: cvc doesn't care if it's integer or real ?
	// needed as Lifter distinguishes between Cvc3Int and Cvc3Real
	else if (type.equals(typeInt) && eType.equals(typeReal)) {
	    return expr;
	    //return prover.funExpr(realToInt, expr);
	} else if (type.equals(typeReal) && eType.equals(typeInt)) {
	    //return prover.funExpr(intToReal, expr);
	    return expr;
	}

	// ref <-> type
	// e.g needed in: (NEQ (|getClass#| |brokenObj<8>|) null)
	else if (type.equals(typeRef) && eType.equals(typeType)) {
	    return simplifyCast(expr, typeToRef, refToType);
	    //return prover.funExpr(typeToRef, expr);
	} else if (type.equals(typeType) && eType.equals(typeRef)) {
	    return simplifyCast(expr, refToType, typeToRef);
	    //return prover.funExpr(refToType, expr);
	}

	// bool <-> pred
	// can we get away doing nothing?
	// cvc doesn't really care if a int is used as a real,
	// or a real which is actually an int is used as an int.
	else if (type.equals(typePred) && eType.equals(typeBool)) {
	    assert(false);
	    return prover.eqExpr(expr, ((Cvc3Bool)buildBool(true)).getExpr());
	} else if (type.equals(typeBool) && eType.equals(typePred)) {
	    assert(false);
	    return prover.iteExpr(expr, ((Cvc3Bool)buildBool(true)).getExpr(), ((Cvc3Bool)buildBool(false)).getExpr());
	}

	// bool/int/real/ref to value
	else if (type.equals(typeValue)) {
	    if (eType.equals(typeBool)) {
		return simplifyCast(expr, boolToValue, valueToBool);
		//return prover.funExpr(boolToValue, expr);
	    } else if (eType.equals(typeInt)) {
		return simplifyCast(expr, intToValue, valueToInt, valueToReal);
		/*
		if (expr.isApply() && expr.getOp().equals(valueToInt)) {
		    System.out.println (valueToInt);
		    assert(expr.arity() == 1);
		    return expr.getChild(0);
			//if (op.getExpr().equals(valueToInt.getExpr())) {
			//System.out.println ("intToValue of: " + expr);
			//System.out.println (expr.arity());
			//System.out.println (expr.getChild(0));
		}
		return prover.funExpr(intToValue, expr);
		*/
	    } else if (eType.equals(typeReal)) {
		return simplifyCast(expr, realToValue, valueToReal, valueToReal);
		//return prover.funExpr(realToValue, expr);
	    } else if (eType.equals(typeRef)) {
		return simplifyCast(expr, refToValue, valueToRef);
		//return prover.funExpr(refToValue, expr);
	    }
	}
	// value to bool/int/real/ref
	else if (type.equals(typeBool)) {
	    if (eType.equals(typeValue)) {
		return simplifyCast(expr, valueToBool, boolToValue);
		//return prover.funExpr(valueToBool, expr);
	    }
	} else if (type.equals(typeInt)) {
	    if (eType.equals(typeValue)) {
		return simplifyCast(expr, valueToInt, intToValue, realToValue);
		//return prover.funExpr(valueToInt, expr);
	    }
	} else if (type.equals(typeReal)) {
	    if (eType.equals(typeValue)) {
		return simplifyCast(expr, valueToReal, realToValue, intToValue);
		//return prover.funExpr(valueToReal, expr);
	    }
	} else if (type.equals(typeRef)) {
	    if (eType.equals(typeValue)) {
		return simplifyCast(expr, valueToRef, refToValue);
		//return prover.funExpr(valueToRef, expr);
	    }	    
	}
	/*
	// bool/int/real/ref field instances to field
	else if (type.equals(typeField)) {
	    if (eType.equals(typeBoolField)) {
		return simplifyCast(expr, boolFieldToField, fieldToBoolField);
		//return prover.funExpr(boolFieldToField, expr);
	    } else if (eType.equals(typeIntField)) {
		return simplifyCast(expr, intFieldToField, fieldToIntField);
		//return prover.funExpr(intFieldToField, expr);
	    } else if (eType.equals(typeRealField)) {
		return simplifyCast(expr, realFieldToField, fieldToRealField);
		//return prover.funExpr(realFieldToField, expr);
	    } else if (eType.equals(typeRefField)) {
		return simplifyCast(expr, refFieldToField, fieldToRefField);
		//return prover.funExpr(refFieldToField, expr);
	    }
	}
	// field to bool/int/real/ref field instances
	else if (type.equals(typeBoolField)) {
	    if (eType.equals(typeField)) {
		return simplifyCast(expr, fieldToBoolField, boolFieldToField);
		//return prover.funExpr(fieldToBoolField, expr);
	    }
	} else if (type.equals(typeIntField)) {
	    if (eType.equals(typeField)) {
		return simplifyCast(expr, fieldToIntField, intFieldToField);
		//return prover.funExpr(fieldToIntField, expr);
	    }
	} else if (type.equals(typeRealField)) {
	    if (eType.equals(typeField)) {
		return simplifyCast(expr, fieldToRealField, realFieldToField);
		//return prover.funExpr(fieldToRealField, expr);
	    }
	} else if (type.equals(typeRefField)) {
	    if (eType.equals(typeField)) {
		return simplifyCast(expr, fieldToRefField, refFieldToField);
		//return prover.funExpr(fieldToRefField, expr);
	    }
	}
	*/
	ErrorSet.fatal("cast: " + eType + " <---> " + type);
	assert(false);
	return expr;
    }


    //
    // wrap an expression in an esc node corresponding to the given sort
    //
    // this doesn't mean that the contained expression is of the corresponding type,
    // just that it is convertible.
    // E.g. a Cvc3Int can contain an expression of type typeReal.
    //


    Cvc3Term wrapExpr(Expr e) throws Cvc3Exception {
	return wrapExpr(e, e.getType());
    }

    Cvc3Term wrapExpr(Expr e, Sort sort) throws Cvc3Exception {
	return wrapExpr(e, mapValSort(sort));
    }

    Cvc3Term wrapExpr(Expr e, Type type) throws Cvc3Exception {
	if (type.equals(typePred)) {
	    return new Cvc3Pred(e);
	} else if (type.equals(typeValue)) {
	    return new Cvc3Value(e);
	} else if (type.equals(typeBool)) {
	    return new Cvc3Bool(e);
	} else if (type.equals(typeInt)) {
	    return new Cvc3Int(e);
	} else if (type.equals(typeReal)) {
	    return new Cvc3Real(e);
	} else if (type.equals(typeRef)) {
	    return new Cvc3Ref(e);
	} else if (type.equals(typeString)) {
	    assert(sortString.isSubSortOf(sortRef));
	    return new Cvc3Ref(e);

	} else if (type.equals(typeShape)) {
	    assert(sortShape.isSubSortOf(sortAny));
	    return new Cvc3Any(e);
	} else if (type.equals(typeTime)) {
	    assert(sortTime.isSubSortOf(sortInt));
	    return new Cvc3Int(e);
	} else if (type.equals(typeType)) {
	    assert(sortType.isSubSortOf(sortRef));
	    return new Cvc3Ref(e);
	} else if (type.equals(typeLock)) {
	    assert(sortType.isSubSortOf(sortRef));
	    return new Cvc3Ref(e);
	    
	} else if (type.equals(typeField)
		   ||
		   type.equals(typeBoolField)
		   ||
		   type.equals(typeIntField)
		   ||
		   type.equals(typeRealField)
		   ||
		   type.equals(typeRefField)
		   ||
		   type.equals(typeArray)
		   ||
		   type.equals(typeElems)
		   ||
		   type.equals(typeLockSet)) {
	    return new Cvc3Map(e);
	} else {
	    System.out.println("wrapexpr failed");
	    System.out.println(e);
	    System.out.println(type);
	    assert (false);
	    return new Cvc3Term();
	}
    }



    
    //
    // NodeBuilder interface
    //

    protected String integralPrintName(long n) {
	Cvc3Prover.print("!integralPrintName");
	assert(false);
	return String.valueOf(n);
    }

    public SAny buildFnCall(FnSymbol fn, SAny[] args) {
	Cvc3Prover.print("!buildFnCall: " + fn);
	for (int i = 0; i < args.length; ++i) {
	    Cvc3Prover.print("  " + args[i]);
	}
	assert(fn.retType != sortPred);
	// :TODO: check if stuff we omitted when translating the background predicate
	assert(fn != symArrayMake);
	assert(fn != symIsNewArray);
	/* Lifter public vars, not static though
	assert(fn != symValueToBool);
	assert(fn != symValueToInt);
	assert(fn != symValueToReal);
	assert(fn != symValueToRef);
	assert(fn != symValueToPred);
	assert(fn != symBoolToValue);
	assert(fn != symIntToValue);
	assert(fn != symRealToValue);
	assert(fn != symRefToValue);
	assert(fn != symIntToReal);
	assert(fn != symRealToInt);
	assert(fn != symPredToBool); */
	assert(fn != symNonNullElems);
	assert(!fn.name.equals("intFirst"));
	assert(!fn.name.equals("intLast"));
	assert(!fn.name.equals("longFirst"));
	assert(!fn.name.equals("longLast"));
	assert(!fn.name.equals("arrayMake"));
	assert(!fn.name.equals("arrayType"));
	// :TODO: test495 StackCheck.java assert(!fn.name.equals("unset"));
	//assert(!fn.name.equals("stringCat"));
	//assert(!fn.name.equals("stringCatP"));
	assert(!fn.name.equals("next"));
	assert(!fn.name.equals("integralEQ"));
	assert(!fn.name.equals("integralLE"));
	assert(!fn.name.equals("integralLT"));
	assert(!fn.name.equals("integralGE"));
	assert(!fn.name.equals("integralGT"));
	assert(!fn.name.equals("integralNE"));
	assert(!fn.name.equals("integralAnd"));
	assert(!fn.name.equals("integralOr"));
	assert(!fn.name.equals("integralDiv"));
	assert(!fn.name.equals("integralXor"));
	assert(!fn.name.equals("integralMod"));
	assert(!fn.name.equals("intShiftL"));
	assert(!fn.name.equals("longShiftL"));
	assert(!fn.name.equals("floatingEQ"));
	assert(!fn.name.equals("floatingLE"));
	assert(!fn.name.equals("floatingLT"));
	assert(!fn.name.equals("floatingGE"));
	assert(!fn.name.equals("floatingGT"));
	assert(!fn.name.equals("floatingNE"));
	assert(!fn.name.equals("floatingADD"));
	assert(!fn.name.equals("floatingMUL"));
	assert(!fn.name.equals("floatingMOD"));
	assert(!fn.name.equals("refEQ"));
	assert(!fn.name.equals("refNE"));
	//	assert(!fn.name.equals(symAsChild.name));
	try {
	    List key = Arrays.asList(new Object[] { "buildFnCall", uniqueName(fn), args });

	    Expr expr;
	    //Type rType;
	    if (escMap.containsKey(key)) {
		return (Cvc3Any) escMap.get(key);
	    } else if (args.length == 0) {
		expr = mapValSymbol(fn);
		//rType = expr.getType();
	    } else {
		Op f = mapFunSymbol(fn);
		if (fn == symAsField) {
		    //System.out.println("ASFIELD");
		    //assert (args.length == 2);
		    Type fieldType = ((Cvc3Any)args[0]).getExpr().getType();
		    if (fieldType.equals(typeBoolField)) {
			f = asFieldBool;
		    } else if (fieldType.equals(typeIntField)) {
			f = asFieldInt;
		    } else if (fieldType.equals(typeRealField)) {
			f = asFieldReal;
		    } else if (fieldType.equals(typeRefField)) {
			f = asFieldRef;
		    } else {
			System.out.println(args[0]);
			System.out.println(fieldType);
			assert(false);
		    }
		    /*		} else if (fn == symFClosedTime) {
		    System.out.println("FCLOSEDTIME");
		    assert (args.length == 1);
		    Type fieldType = ((Cvc3Any)args[0]).getExpr().getType();
		    if (fieldType.equals(typeBoolField)) {
			f = fClosedTimeBool;
		    } else if (fieldType.equals(typeIntField)) {
			f = fClosedTimeInt;
		    } else if (fieldType.equals(typeRealField)) {
			f = fClosedTimeReal;
		    } else if (fieldType.equals(typeRefField)) {
			f = fClosedTimeRef;
		    } else {
			System.out.println(args[0]);
			System.out.println(fieldType);
			assert(false);
			}*/
		} else {
		    f = mapFunSymbol(fn);
		}
		Type fType = f.getExpr().getType();
		assert(fType.isFunction());
		assert(fType.arity() == args.length + 1);
		List children = new ArrayList();//cast((Cvc3Any[])args, fType);
		for (int i = 0; i < args.length; ++i) {
		    //assert(escMap.containsKey(args[i]));
		    Expr e = cast(((Cvc3Any)args[i]).getExpr(), fType.getChild(i));
		    children.add(e);
		}
	
		expr = prover.funExpr(f, children);
	    }
	    
	    Cvc3Any node = (Cvc3Any) wrapExpr(expr, fn.retType);
	    escMap.put(key, node);
	    return node;

	} catch (cvc3.Cvc3Exception e) {
	    ErrorSet.fatal(e.toString());
	    throw new Error(e);
	}
    }

    public SAny buildConstantRef(FnSymbol c) {
	Cvc3Prover.print("!buildConstantRef: " + c);
	return new Cvc3Any();
    }

    public SAny buildQVarRef(QuantVar v) {
	Cvc3Prover.print("!buildQVarRef: " + v);
	return getBoundVarExpr(v);
    }

    //@ requires \nonnullelements(args);
    public SPred buildPredCall(PredSymbol fn, SAny[] args) {
	Cvc3Prover.print("!buildPredCall: " + fn + " " + args);
	for (int i = 0; i < args.length; ++i) {
	    Cvc3Prover.print("  " + args[i]);
	}
	assert(fn.retType == sortPred);

	// these are used to convert predicates to functions of type bool,
	// where cvc uses boolToPred / predToBool instead
	assert(!fn.name.equals("boolAnd"));
	assert(!fn.name.equals("boolEq"));
	assert(!fn.name.equals("boolImplies"));
	assert(!fn.name.equals("boolNE"));
	assert(!fn.name.equals("boolNot"));
	assert(!fn.name.equals("boolOr"));

	// symRefEQ is rewritten to =
	if (fn == symRefEQ) {
	    assert(args.length == 2);
	    return buildAnyEQ(args[0], args[1]);
	}
	if (fn == symRefNE) {
	    assert(args.length == 2);
	    return buildAnyNE(args[0], args[1]);
	}

	// symTypeEq is rewritten to =
	if (fn == symTypeEQ) {
	    assert(args.length == 2);
	    return buildAnyEQ(args[0], args[1]);
	}
	if (fn == symTypeNE) {
	    assert(args.length == 2);
	    return buildAnyNE(args[0], args[1]);
	}

	//(DEFPRED (isAllocated x a0) (< (vAllocTime x) a0))
	if (optIsallocated && fn == symIsAllocated) {
	    assert(args.length == 2);
	    SAny t = buildFnCall(symvAllocTime, new SAny[] { args[0] });
	    return buildArithPred(predLT, (SInt)t, (SInt)args[1]);
        }

	if (fn == symAllocLE) {
	    assert(args.length == 2);
	    return buildArithPred(
	      predLE,
	      buildValueConversion(sortRef, sortValue, (SValue)args[0]),
	      buildValueConversion(sortRef, sortValue, (SValue)args[1]));
	}
	//(DEFPRED (lockLT x y) (< x y))
	if (fn == symAllocLT) {
	    assert(args.length == 2);
	    return buildArithPred(
	      predLT,
	      buildValueConversion(sortRef, sortValue, (SValue)args[0]),
	      buildValueConversion(sortRef, sortValue, (SValue)args[1]));
	}

	//:TODO: replacing orderings over locks (i.e. sortRef) by
	// arithmetic ordering, needs cast: ref -> value -> int
	// perhaps just axiomatizing the DEFPRED's might be faster?
	//(DEFPRED (lockLE x y) (<= x y))
	if (fn == symLockLE) {
	    assert(args.length == 2);
	    return buildArithPred(
	      predLE,
	      buildValueConversion(sortRef, sortValue, (SValue)args[0]),
	      buildValueConversion(sortRef, sortValue, (SValue)args[1]));
	}
	//(DEFPRED (lockLT x y) (< x y))
	if (fn == symLockLT) {
	    assert(args.length == 2);
	    return buildArithPred(
	      predLT,
	      buildValueConversion(sortRef, sortValue, (SValue)args[0]),
	      buildValueConversion(sortRef, sortValue, (SValue)args[1]));
	}
	//(DEFPRED (nonnullelements x e)
	//   (AND (NEQ x null)
	//	(FORALL (i)
	//	   (IMPLIES (AND (<= 0 i)
	//			 (< i (arrayLength x)))
	//		    (NEQ (select (select e x) i) null)))))
	if (optNonnullelements && fn == symNonNullElems) {
	    assert(args.length == 2);
	    SValue x = (SValue) args[0];
	    SValue e = (SValue) args[1];
	    QuantVar vi = registerQuantifiedVariable("i", sortInt);
	    SAny t0 = buildFnCall(symArrayLength, new SAny[] { x });
	    SAny t1 = buildSelect((SMap)e, x);
	    SAny t2 = buildSelect((SMap)t1, (SInt)buildQVarRef(vi));
	    SPred p0 = buildAnyNE(x, buildNull());
	    SPred p1 = buildIntPred(predLE, buildInt(0), (SInt)buildQVarRef(vi));
	    SPred p2 = buildIntPred(predLT, (SInt)buildQVarRef(vi), (SInt)t0);
	    SPred p3 = buildAnyNE(t2, buildNull());
	    SPred p4 = buildAnd(new SPred[] { p1, p2 } );
	    SPred p5 = buildImplies(p4, p3);
	    QuantVar[] vars0 = new QuantVar[] { vi };
	    SPred p6 = buildForAll(vars0, p5, null, null);
	    SPred p7 = buildAnd(new SPred[] { p0, p6 } );
	    return p7;
	}
	try {
	    List key = Arrays.asList(new Object[] { "buildPredCall", uniqueName(fn), args });

	    Expr expr;
	    if (escMap.containsKey(key)) {
		return (Cvc3Pred) escMap.get(key);
	    } else if (args.length == 0) {
		expr = mapValSymbol(fn);
		//rType = expr.getType();
	    } else {
		Op f = mapPredSymbol(fn);
		Type fType = f.getExpr().getType();
		assert(fType.arity() == args.length + 1);
		List children = new ArrayList();
		for (int i = 0; i < args.length; ++i) {
		    //assert(escMap.containsKey(args[i]));
		    Expr e = cast(((Cvc3Term)args[i]).getExpr(), fType.getChild(i));
		    children.add(e);
		}
		
		expr = prover.funExpr(f, children);
	    }
	    Cvc3Pred node = new Cvc3Pred(expr);
	    return registerCvc3Pred(key, node);

	} catch (cvc3.Cvc3Exception e) {
	    ErrorSet.fatal(e.toString());
	    throw new Error(e);
	}
    }
	

    // Boolean connectives

    public SPred buildImplies(SPred _arg1, SPred _arg2) {
	Cvc3Prover.print("!buildImplies: " + _arg1 + " " + _arg2);
	return buildOr(buildNot(_arg1), _arg2);
    }

    public SPred buildIff(SPred _arg1, SPred _arg2) {
	Cvc3Prover.print("!buildIff: " + _arg1 + " " + _arg2);
	return buildAnd(buildImplies(_arg1, _arg2), buildImplies(_arg2, _arg1));
    }

    public SPred buildXor(SPred _arg1, SPred _arg2) {
	Cvc3Prover.print("!buildXor: " + _arg1 + " " + _arg2);
	return buildNot(buildIff(_arg1, _arg2));
    }

    public SPred buildAnd(SPred _arg1, SPred _arg2) {
	SPred[] args = { _arg1, _arg2 };
	return buildAnd(args);
    }

    public SPred buildAnd(SPred[] args) {
	Cvc3Prover.print("!buildAnd: " + args);
	for (int i = 0; i < args.length; ++i) {
	    Cvc3Prover.print("  " + args[i]);
	}
	try {
	    List key = Arrays.asList(new Object[] { "buildAnd", args });
	    if (escMap.containsKey(key)) {
		return (Cvc3Pred) escMap.get(key);
	    } else {
		Cvc3Pred node = null;
		boolean rewritten = false;
		if (rewrite) {
		    for (int i = 0; !rewritten && i < args.length; ++i) {
			Expr ci = ((Cvc3Pred)args[i]).getExpr();
			if (ci.equals(prover.falseExpr())
			    //||
			    //(rewriteCvc3 && prover.simplify(ci).equals(prover.falseExpr()))
			    ) {
			    rewritten = true;
			    node = transferLabels((Cvc3Pred)args[i], (Cvc3Pred)buildFalse());
			}
		    }

		    // p and -p
		    for (int i = 0; !rewritten && i < args.length - 1; ++i) {
			Expr ci = ((Cvc3Pred)args[i]).getExpr();
			for (int j = 0; !rewritten && i < args.length; ++i) {
			    Expr cj = ((Cvc3Pred)args[i]).getExpr();
			    if (ci.equals(prover.notExpr(cj)) || cj.equals(prover.notExpr(ci))) {
				rewritten = true;
				node = transferLabels((Cvc3Pred)args[i], (Cvc3Pred)buildFalse());
				node = transferLabels((Cvc3Pred)args[j], node);
			    }
			}
		    }
		}
		if (!rewritten) {
		    List children = new ArrayList();
		    List childrenExpr = new ArrayList();
		    //:TODO: omitted needs to be moved to left child, not to parent node
		    List omitted = new ArrayList();
		    for (int i = 0; i < args.length; ++i) {
			Expr ci = ((Cvc3Pred)args[i]).getExpr();
			if (!ci.equals(prover.trueExpr())
			    //||
			    //(rewriteCvc3 && prover.simplify(ci).equals(prover.trueExpr()))
			    ) {
			    children.add(args[i]);
			    childrenExpr.add(((Cvc3Pred)args[i]).getExpr());
			} else {
			    omitted.add(args[i]);
			}
		    }
		    if (children.size() == 0) {
			node = (Cvc3Pred) buildTrue();
		    } else if (children.size() == 1) {
			node = (Cvc3Pred) children.get(0);
		    } else {
			node = new Cvc3Pred(prover.andExpr(childrenExpr));
			Iterator i = children.iterator();
			while (i.hasNext()) {
			    node.addChild((Cvc3Pred)i.next());
			}
			assert(node.getExpr().arity() == node.getChildren().size());
			assert(args.length >= node.getExpr().arity());
		    }
		    //node = transferLabels(omitted, node);
		}
		escMap.put(key, node);
		return node;
	    }
	} catch (cvc3.Cvc3Exception e) {
	    ErrorSet.fatal(e.toString());
	    throw new Error(e);
	}
    }

    public SPred buildOr(SPred _arg1, SPred _arg2) {
	SPred[] args = { _arg1, _arg2 };
	return buildOr(args);
    }

    public SPred buildOr(SPred[] args) {
	Cvc3Prover.print("!buildOr: " + args);
	for (int i = 0; i < args.length; ++i) {
	    Cvc3Prover.print("  " + args[i]);
	}
	try {
	    List key = Arrays.asList(new Object[] { "buildOr", args });
	    if (escMap.containsKey(key)) {
		return (Cvc3Pred) escMap.get(key);
	    } else {
		Cvc3Pred node = null;
		boolean rewritten = false;
		if (rewrite) {
		    // true or p
		    for (int i = 0; !rewritten && i < args.length; ++i) {
			Expr ci = ((Cvc3Pred)args[i]).getExpr();
			if (ci.equals(prover.trueExpr())
			    //||
			    //(rewriteCvc3 && prover.simplify(ci).equals(prover.trueExpr()))
			    ) {
			    rewritten = true;
			    node = transferLabels((Cvc3Pred)args[i], (Cvc3Pred)buildTrue());
			}
		    }

		    // p or -p
		    for (int i = 0; !rewritten && i < args.length - 1; ++i) {
			Expr ci = ((Cvc3Pred)args[i]).getExpr();
			for (int j = 0; !rewritten && i < args.length; ++i) {
			    Expr cj = ((Cvc3Pred)args[i]).getExpr();
			    if (ci.equals(prover.notExpr(cj)) || cj.equals(prover.notExpr(ci))) {
				rewritten = true;
				node = transferLabels((Cvc3Pred)args[i], (Cvc3Pred)buildTrue());
				node = transferLabels((Cvc3Pred)args[j], node);
				//node = (Cvc3Pred)buildTrue();
			    }
			}
		    }
		}
		if (!rewritten) {
		    List children = new ArrayList();
		    List childrenExpr = new ArrayList();
		    List omitted = new ArrayList();
		    for (int i = 0; i < args.length; ++i) {
			Expr ci = ((Cvc3Pred)args[i]).getExpr();
			if (!ci.equals(prover.falseExpr())
			    //||
			    //(rewriteCvc3 && prover.simplify(ci).equals(prover.trueExpr()))
			    ) {
			    children.add(args[i]);
			    childrenExpr.add(((Cvc3Pred)args[i]).getExpr());
			} else {
			    omitted.add(args[i]);
			}
		    }
		    if (children.size() == 0) {
			//:TODO: label
			//:TODO: cache, also for rewritting, simplify and of length 1
			node = (Cvc3Pred) buildFalse();
		    } else if (children.size() == 1) {
			node = (Cvc3Pred) children.get(0);
		    } else {
			node = new Cvc3Pred(prover.orExpr(childrenExpr));
			Iterator i = children.iterator();
			while (i.hasNext()) {
			    node.addChild((Cvc3Pred)i.next());
			}
			assert(node.getExpr().arity() == node.getChildren().size());
			assert(args.length >= node.getExpr().arity());
		    }
		    //node = transferLabels(omitted, node, false);
		}
		escMap.put(key, node);
		return node;
	    }
	} catch (cvc3.Cvc3Exception e) {
	    ErrorSet.fatal(e.toString());
	    throw new Error(e);
	}
    }


    public SPred buildNot(SPred _arg) {
	Cvc3Pred arg = (Cvc3Pred) _arg;
	Cvc3Prover.print("!buildNot: " + arg);
	try {
	    List key = Arrays.asList(new Object[] { "buildNot", arg });
	    if (escMap.containsKey(key)) {
		return (Cvc3Pred) escMap.get(key);
	    } else {
		Expr e1 = arg.getExpr();
		
		Cvc3Pred node = null;
		boolean rewritten = false;
		if (rewrite) {
		    //:TODO: move labels
		    if (e1.equals(prover.trueExpr())
			//			||
			//			(rewriteCvc3 && prover.simplify(e1).equals(prover.trueExpr()))
			) {
			assert(arg.isLabeled() == arg instanceof Cvc3Label);
			rewritten = true;
			node = transferLabels(arg, (Cvc3Pred) buildFalse(), true);
		    } else if (e1.equals(prover.falseExpr())
			       //			       ||
			       //			       (rewriteCvc3 && prover.simplify(e1).equals(prover.falseExpr()))
			       ) {
			assert(arg.isLabeled() == arg instanceof Cvc3Label);
			rewritten = true;
			node = transferLabels(arg, (Cvc3Pred) buildTrue(), true);
		    } else if (e1.isNot()) {
                        // e1 = not e2
			rewritten = true;
			// unwrap all labels
			Cvc3Pred unwrap = arg;
			while (unwrap instanceof Cvc3Label) {
			    assert (unwrap.getChildren().size() == 1);
			    unwrap = (Cvc3Pred) unwrap.getChildren().get(0);
			}
			// extract negated expression
			assert (unwrap.getExpr().equals(e1));
			assert (unwrap.getChildren().size() == 1);
                        // e2
			node = (Cvc3Pred) unwrap.getChildren().get(0);
                        // move labels from e1 to e2
			node = transferLabels(arg, node, true);
		    }
		}
		if (!rewritten) {
		    node = new Cvc3Pred(prover.notExpr(e1));
		    node.addChild(arg);
		}
		escMap.put(key, node);
		return node;
	    }
	} catch (cvc3.Cvc3Exception e) {
	    ErrorSet.fatal(e.toString());
	    throw new Error(e);
	}
    }

    public SPred buildTrue() {
	Cvc3Prover.print("!buildTrue: ");
	return escTrue;
    }
	
    public SPred buildFalse() {
	Cvc3Prover.print("!buildFalse: ");
	return escFalse;
    }

    public SPred buildDistinct(SAny[] terms) {
	Cvc3Prover.print("!buildDistinct: " + terms);
	for (int i = 0; i < terms.length; ++i) {
	    Cvc3Prover.print("  " + terms[i]);
	}

	List key = Arrays.asList(new Object[] { "buildDistinct", terms });
	if (escMap.containsKey(key)) {
	    return (Cvc3Pred) escMap.get(key);
	} else {
	    SPred[] pairs = new SPred[(terms.length * (terms.length - 1)) / 2];
	    int counter = 0;
	    for (int i = 0; i < terms.length - 1; ++i) {
		for (int j = i + 1; j < terms.length; ++j) {
		    pairs[counter] = buildAnyNE(terms[i], terms[j]);
		    ++counter;
		}
	    }
	    
	    Cvc3Pred node = (Cvc3Pred) buildAnd(pairs);
	    escMap.put(key, node);
	    return node;
	}
    }

    public SPred buildLabel(boolean pos, String name, SPred _pred) {
	Cvc3Pred pred = (Cvc3Pred) _pred;
	Cvc3Prover.print("!buildLabel: " + name + " " + pred);	
	try {
	    List key = Arrays.asList(new Object[] { "buildLabel", new Boolean(pos), name, pred });
	    if (escMap.containsKey(key)) {
		return (Cvc3Pred) escMap.get(key);
	    } else {
		Cvc3Pred node = null;
		// label not relevant: false LBLPOS or true LBLNEG
		if (
		    (pos && pred.getExpr().equals(prover.falseExpr()))
		    ||
		    (!pos && pred.getExpr().equals(prover.trueExpr()))
		    ) {
		    node = pred;
		}
		// create new label
		else {		
		    node = new Cvc3Label(pos, name, pred);
		}
		escMap.put(key, node);
		return node;
	    }
        } catch (cvc3.Cvc3Exception e) {
	    ErrorSet.fatal(e.toString());
	    throw new Error(e);
	}
    }
	
    public SValue buildITE(SPred _cond, SValue _then_part, SValue _else_part) {
	Cvc3Pred cond = (Cvc3Pred) _cond;
	Cvc3Value then_part = (Cvc3Value) _then_part;
	Cvc3Value else_part = (Cvc3Value) _else_part;
	Cvc3Prover.print("!buildITE: " + cond + " " + then_part + " " + else_part);

	try {
	    List key = Arrays.asList(new Object[] { "buildITE", cond, then_part, else_part });
	    if (escMap.containsKey(key)) {
		return (Cvc3Value) escMap.get(key);
	    } else {
		// :TODO: labels not supported within ITE
		assert(!cond.isLabeled());

		Cvc3Value node = null;
		if (rewrite && cond.getExpr().equals(prover.trueExpr())) {
                    node = then_part;
		} else if (rewrite && cond.getExpr().equals(prover.falseExpr())) {
                    node = then_part;
		} else {
		    Type t = unify(then_part.getExpr().getType(), else_part.getExpr().getType());
		    node = new Cvc3Value(prover.iteExpr(
						       cond.getExpr(),
						       cast(then_part.getExpr(), t),
						       cast(else_part.getExpr(), t)));
		}
		escMap.put(key, node);
		return node;
	    }
	    
	} catch (cvc3.Cvc3Exception e) {
	    ErrorSet.fatal(e.toString());
	    throw new Error(e);
	}
    }
    
    //@ requires \nonnullelements(vars);
    //@ requires pats != null ==> \nonnullelements(pats);
    //@ requires pats != null ==> \nonnullelements(nopats);
    public SPred buildForAll(QuantVar[] vars, SPred _body, STerm[][] pats, STerm[] nopats) {
	Cvc3Pred body = (Cvc3Pred) _body;
	Cvc3Prover.print("!buildForAll: " + vars + " " + body
	      + " " + pats + " " + nopats);
	try {
	    if (rewrite
		&&
		(body.getExpr().equals(prover.falseExpr())
		 || body.getExpr().equals(prover.trueExpr()))
		) {
		return _body;
	    }
	    List key = Arrays.asList(new Object[] { "buildForAll", vars, body, pats, nopats });
	    if (escMap.containsKey(key)) {
		return (Cvc3Pred) escMap.get(key);
	    } else {
		List varExprs = new ArrayList();
		for (int i = 0; i < vars.length; ++i) {
		    varExprs.add(getBoundVarExpr(vars[i]).getExpr());
		}

		// triggers: STerm[][]pats
		// - each list in pats represents a trigger
		// - each trigger consists of a set of expressions,
		//   i.e. a multi-trigger consists of more than one expression
		List triggers = new ArrayList();
		if (optManualTriggers && pats != null && pats.length > 0) {
		    Cvc3Prover.print("TRIGGERS: ");

		    //List triggers = new ArrayList();
		    for (int i = 0; i < pats.length; ++i) {
			assert(pats[i].length > 0);
			if (pats[i].length > 1) {
			    Cvc3Prover.print("MULTI-TRIGGER: ");
			    if (!optMultiTriggers) continue;
			}
			List trigger = new ArrayList();
			for (int j = 0; j < pats[i].length; ++j) {
			    Cvc3Prover.print("  TRIGGER: " + ((Cvc3Term)pats[i][j]).getExpr());
			    trigger.add(((Cvc3Term)pats[i][j]).getExpr());
			}
			triggers.add(prover.listExpr(trigger));
		    }
		}
		Expr e = prover.forallExpr(varExprs, body.getExpr(), triggers);

		Cvc3Pred node = new Cvc3Pred(e);
		node.addChild(body);
		escMap.put(key, node);
		return node;
	    }
	} catch (cvc3.Cvc3Exception e) {
	    ErrorSet.fatal(e.toString());
	    throw new Error(e);
	}
    }

    //@ requires \nonnullelements(vars);
    public SPred buildExists(QuantVar[] vars, SPred _body) {
	Cvc3Pred body = (Cvc3Pred) _body;
	Cvc3Prover.print("!buildExists: " + vars + " " + body);
	try {
	    List key = Arrays.asList(new Object[] { "buildExists", vars, body });
	    if (escMap.containsKey(key)) {
		return (Cvc3Pred) escMap.get(key);
	    } else {
		List varExprs = new ArrayList();
		for (int i = 0; i < vars.length; ++i) {
		    varExprs.add(getBoundVarExpr(vars[i]).getExpr());
		}
		Cvc3Pred node = new Cvc3Pred(prover.existsExpr(varExprs, body.getExpr()));
		node.addChild(body);
		escMap.put(key, node);
		return node;
	    }
	} catch (cvc3.Cvc3Exception e) {
	    ErrorSet.fatal(e.toString());
	    throw new Error(e);
	}
    }
	

    // Arithmetic

    //@ requires predFirst <= realPredTag && realPredTag <= predLast;
    public SPred buildArithPred(int arithPredTag, SValue _arg1, SValue _arg2) {
	Cvc3Value arg1 = (Cvc3Value) _arg1;
	Cvc3Value arg2 = (Cvc3Value) _arg2;
	Cvc3Prover.print("!buildArithPred: " + arithPredTag + " " + arg1 + " " + arg2);
	try {
	    List key = Arrays.asList(new Object[] { "buildArithPred", new Integer(arithPredTag), arg1, arg2 });
	    if (escMap.containsKey(key)) {
		return (Cvc3Pred) escMap.get(key);
	    } else {
		// :TODO: should need cast only if arg is value -
		// but is this already automatically done in the vc?
		Expr e1 = cast(arg1.getExpr(), typeReal); 
		Expr e2 = cast(arg2.getExpr(), typeReal);

		/* never happens
		while (sameCast(e1, e2) && isArithType(e1.getChild(0))) {
		    e1 = e1.getChild(0);
		    e2 = e2.getChild(0);
		    assert(isArithType(e1));
		    assert(isArithType(e2));
		}
		*/

		//Expr e1 = arg1.getExpr();
		//Expr e2 = arg2.getExpr();
		Cvc3Pred node = null;
		switch (arithPredTag) {
		case predGE: node = new Cvc3Pred(prover.geExpr(e1, e2)); break;
		case predLE: node = new Cvc3Pred(prover.leExpr(e1, e2)); break;
		case predGT: node = new Cvc3Pred(prover.gtExpr(e1, e2)); break;
		case predLT: node = new Cvc3Pred(prover.ltExpr(e1, e2)); break;
		case predEQ: node = (Cvc3Pred) buildAnyEQ(arg1, arg2); break;
		case predNE: node = (Cvc3Pred) buildAnyNE(arg1, arg2); break;
		default:
		    ErrorSet.fatal("buildRealPred"); assert(false);
		}

		return registerCvc3Pred(key, node);
	    }
	} catch (cvc3.Cvc3Exception e) {
	    ErrorSet.fatal(e.toString());
	    throw new Error(e);
	}
    }


    //@ requires predFirst <= intPredTag && intPredTag <= predLast;
    public SPred buildIntPred(int intPredTag, SInt arg1, SInt arg2) {
	Cvc3Prover.print("!buildIntPred: " + intPredTag + " " + arg1 + " " + arg2);
	return buildArithPred(intPredTag, arg1, arg2);
    }
	
    //@ requires predFirst <= realPredTag && realPredTag <= predLast;
    public SPred buildRealPred(int realPredTag, SReal arg1, SReal arg2) {
	Cvc3Prover.print("!buildRealPred: " + realPredTag + " " + arg1 + " " + arg2);
	return buildArithPred(realPredTag, arg1, arg2);
    }

    //@ requires predFirst <= realPredTag && realPredTag <= predLast;
    public SBool buildArithBoolFun(int arithPredTag, SValue arg1, SValue arg2) {
	Cvc3Prover.print("!buildArithBoolFun: " + arithPredTag + " " + arg1 + " " + arg2);
	//assert(false);
	try {
	    List key = Arrays.asList(new Object[] { "buildArithBoolFun", new Integer(arithPredTag), arg1, arg2 });
	    if (escMap.containsKey(key)) {
		return (Cvc3Bool) escMap.get(key);
	    } else {
		Cvc3Pred p = (Cvc3Pred) buildArithPred(arithPredTag, arg1, arg2);
		Cvc3Bool node = (Cvc3Bool) wrapExpr(cast(p.getExpr(), sortBool));
		escMap.put(key, node);
		return node;
	    }
	} catch (cvc3.Cvc3Exception e) {
	    ErrorSet.fatal(e.toString());
	    throw new Error(e);
	}
    }

    //@ requires predFirst <= intPredTag && intPredTag <= predLast;
    public SBool buildIntBoolFun(int intPredTag, SInt arg1, SInt arg2) {
	Cvc3Prover.print("!buildIntBoolFun: " + intPredTag + " " + arg1 + " " + arg2);
	return buildArithBoolFun(intPredTag, arg1, arg2);
    }
  
    //@ requires predFirst <= realPredTag && realPredTag <= predLast;
    public SBool buildRealBoolFun(int realPredTag, SReal arg1, SReal arg2) {
	Cvc3Prover.print("!buildRealBoolFun: " + realPredTag + " " + arg1 + " " + arg2);
	return buildArithBoolFun(realPredTag, arg1, arg2);
    }
	
    //@ requires predFirst <= refPredTag && refPredTag <= predLast;
    public SBool buildRefBoolFun(int refPredTag, SRef arg1, SRef arg2) {
	Cvc3Prover.print("!buildRefBoolFun: " + refPredTag + " " + arg1 + " " + arg2);
	return new Cvc3Bool();
    }
    
    //@ requires funFirst <= intFunTag && intFunTag <= funLast;
    public Expr buildArithFun(int arithFunTag, SValue _arg1, SValue _arg2) {
	Cvc3Value arg1 = (Cvc3Value) _arg1;
	Cvc3Value arg2 = (Cvc3Value) _arg2;
	Cvc3Prover.print("!buildArithFun: " + arithFunTag + " " + arg1 + " " + arg2);
	try {
	    Expr e1 = cast(arg1.getExpr(), typeReal); 
	    Expr e2 = cast(arg2.getExpr(), typeReal);

	    /* never happens
	    while (sameCast(e1, e2) && isArithType(e1.getChild(0))) {
		System.out.println("SameCast: B");
		e1 = e1.getChild(0);
		e2 = e2.getChild(0);
		assert(isArithType(e1));
		assert(isArithType(e2));
	    }
	    */

	    switch (arithFunTag) {
	    case funADD: return prover.plusExpr(e1, e2);
	    case funSUB: return prover.minusExpr(e1, e2);
	    case funMUL: return prover.multExpr(e1, e2);
            case funDIV:
	    case funASR32:
	    case funSL32:
	    case funUSR32:
	    case funASR64:
	    case funSL64:
	    case funUSR64:
		throw new UnsupportedOperationException();
	    default:
		ErrorSet.fatal("buildArithFun"); assert(false);
		throw new Error("buildArithFun");
	    }
	} catch (cvc3.Cvc3Exception e) {
	    ErrorSet.fatal(e.toString());
	    throw new Error(e);
	}
    }
    
    //@ requires funFirst <= intFunTag && intFunTag <= funLast;
    public SInt buildIntFun(int intFunTag, SInt arg1, SInt arg2) {
	Cvc3Prover.print("!buildIntFun: " + intFunTag + " " + arg1 + " " + arg2);
	try {
	    List key = Arrays.asList(new Object[] { "buildIntFun", new Integer(intFunTag), arg1, arg2 });
	    if (escMap.containsKey(key)) {
		return (Cvc3Int) escMap.get(key);
	    } else {
		Expr result;
		switch (intFunTag) {
		case funDIV: {
		    Expr exp1 = ((Cvc3Int) arg1).getExpr();
		    Expr exp2 = ((Cvc3Int) arg2).getExpr();
		    result = prover.funExpr(mapFunSymbol(symIntegralDIV), exp1, exp2);
		    break; }
		case funMOD: {
		    Expr exp1 = ((Cvc3Int) arg1).getExpr();
		    Expr exp2 = ((Cvc3Int) arg2).getExpr();
		    result = prover.funExpr(mapFunSymbol(symIntegralMOD), exp1, exp2);
		    break; }
		default:
		    result = buildArithFun(intFunTag, arg1, arg2);
		}
		Cvc3Int node = new Cvc3Int(result);
		escMap.put(key, node);
		return node;
	    }
	} catch (cvc3.Cvc3Exception e) {
	    ErrorSet.fatal(e.toString());
	    throw new Error(e);
	}
    }

    //@ requires funFirst <= realFunTag && realFunTag <= funLast;
    public SReal buildRealFun(int realFunTag, SReal arg1, SReal arg2) {
	Cvc3Prover.print("!buildRealFun: " + realFunTag + " " + arg1 + " " + arg2);
	try {
	    List key = Arrays.asList(new Object[] { "buildRealFun", new Integer(realFunTag), arg1, arg2 });
	    if (escMap.containsKey(key)) {
		return (Cvc3Real) escMap.get(key);
	    } else {
		Expr result;
		switch (realFunTag) {
		case funDIV: {
		    Expr exp1 = ((Cvc3Real) arg1).getExpr();
		    Expr exp2 = ((Cvc3Real) arg2).getExpr();
		    result = prover.funExpr(mapFunSymbol(symFloatingDIV), exp1, exp2);
		    break; }
		case funMOD: {
		    Expr exp1 = ((Cvc3Real) arg1).getExpr();
		    Expr exp2 = ((Cvc3Real) arg2).getExpr();
		    result = prover.funExpr(mapFunSymbol(symFloatingMOD), exp1, exp2);
		    break; }
		default:
		    result = buildArithFun(realFunTag, arg1, arg2);
		}
		Cvc3Real node = new Cvc3Real(result);
		escMap.put(key, node);
		return node;
	    }
	} catch (cvc3.Cvc3Exception e) {
	    ErrorSet.fatal(e.toString());
	    throw new Error(e);
	}
    }
    
    public Expr buildArithFun(int arithFunTag, SValue _arg1) {
	Cvc3Value arg1 = (Cvc3Value) _arg1;
	Cvc3Prover.print("!buildArithFun: " + arithFunTag + " " + arg1);
	try {
	    Expr e = cast(arg1.getExpr(), typeReal);
	    switch (arithFunTag) {
	    case funNEG: return prover.uminusExpr(e);
	    default:
		ErrorSet.fatal("buildArithFun"); assert(false);
		throw new Error("buildArithFun");
	    }
	} catch (cvc3.Cvc3Exception e) {
	    ErrorSet.fatal(e.toString());
	    throw new Error(e);
	}
    }

    //@ requires funUniFirst <= intFunTag && intFunTag <= funUniLast;
    public SInt buildIntFun(int intFunTag, SInt arg1) {
	Cvc3Prover.print("!buildIntFun: " + intFunTag + " " + arg1);
        List key = Arrays.asList(new Object[] { "buildIntFun", new Integer(intFunTag), arg1 });
        if (escMap.containsKey(key)) {
            return (Cvc3Int) escMap.get(key);
        } else {
            Cvc3Int node = new Cvc3Int(buildArithFun(intFunTag, arg1));
            escMap.put(key, node);
            return node;
        }
    }
	
    //@ requires funUniFirst <= realFunTag && realFunTag <= funUniLast;
    public SReal buildRealFun(int realFunTag, SReal arg1) {
	Cvc3Prover.print("!buildRealFun: " + realFunTag + " " + arg1);
        List key = Arrays.asList(new Object[] { "buildRealFun", new Integer(realFunTag), arg1 });
        if (escMap.containsKey(key)) {
            return (Cvc3Real) escMap.get(key);
        } else {
            Cvc3Real node = new Cvc3Real(buildArithFun(realFunTag, arg1));
            escMap.put(key, node);
            return node;
        }
    }
	

    // Literals

    public SBool buildBool(boolean b) {
	Cvc3Prover.print("!buildBool: " + b);
	if (b) {
	    return escBTrue;
	} else {
	    return escBFalse;
	}
    }

    public SInt buildInt(long n) {
	Cvc3Prover.print("!buildInt: " + n);
	try {
	    List key = Arrays.asList(new Object[] { "buildInt", new Long(n) });
	    if (escMap.containsKey(key)) {
		return (Cvc3Int) escMap.get(key);
	    } else {
		Cvc3Int i = new Cvc3Int(prover.ratExpr(Long.toString(n)));
		escMap.put(key, i);
		return i;
	    }
	} catch (cvc3.Cvc3Exception e) {
	    ErrorSet.fatal(e.toString());
	    throw new Error(e);
	}
    }

    public SReal buildReal(double f) {
	Cvc3Prover.print("!buildReal: " + f);
	try {
	    List key = Arrays.asList(new Object[] { "buildReal", new Double(f) });
	    if (escMap.containsKey(key)) {
		return (Cvc3Real) escMap.get(key);
	    } else {
		Cvc3Real r = new Cvc3Real(cast(prover.ratExpr(Double.toString(f)), typeReal));
		assert(!escMap.containsKey(key));
		escMap.put(key, r);
		return r;
	    }
	} catch (cvc3.Cvc3Exception e) {
	    ErrorSet.fatal(e.toString());
	    throw new Error(e);
	}
    }

    public SRef buildNull() {
	Cvc3Prover.print("!buildNull: ");
	return escNull;
    }


    // Maps
	
    public SValue buildSelect(SMap _map, SValue _idx) {
	Cvc3Map map = (Cvc3Map) _map;
	Cvc3Value idx = (Cvc3Value) _idx;
	Cvc3Prover.print("!buildSelect: " + map + " " + idx);
	try {
	    List key = Arrays.asList(new Object[] { "buildSelect", map, idx });
	    if (escMap.containsKey(key)) {
		return (Cvc3Value) escMap.get(key);
	    } else {
		assert(map.getExpr().getType().arity() == 2);
		Type tIndex = map.getExpr().getType().getChild(0);
		Expr expr = prover.readExpr(map.getExpr(), cast(idx.getExpr(), tIndex));
		
		Cvc3Value node = (Cvc3Value) wrapExpr(expr);
		//Cvc3Value node = (Cvc3Value) wrapAnyExpr(expr, map.sort???);
		escMap.put(key, node);
		return node;
	    }
	} catch (cvc3.Cvc3Exception e) {
	    ErrorSet.fatal(e.toString());
	    throw new Error(e);
	}
    }

    public SMap buildStore(SMap _map, SValue _idx, SValue _val) {
	Cvc3Map map = (Cvc3Map) _map;
	Cvc3Value idx = (Cvc3Value) _idx;
	Cvc3Value val = (Cvc3Value) _val;
	Cvc3Prover.print("!buildStore: " + map + " " + idx + " " + val);
	try {
	    List key = Arrays.asList(new Object[] { "buildStore", map, idx, val });
	    if (escMap.containsKey(key)) {
		return (Cvc3Map) escMap.get(key);
	    } else {
		Type type = map.getExpr().getType();
		assert(type.arity() == 2);
		Type tIndex = type.getChild(0);
		Type tValue = type.getChild(1);
		Cvc3Map node = new Cvc3Map(
		  prover.writeExpr(
				   map.getExpr(),
				   cast(idx.getExpr(), tIndex),
				   cast(val.getExpr(), tValue)));
		escMap.put(key, node);
		return node;
	    }
	} catch (cvc3.Cvc3Exception e) {
	    ErrorSet.fatal(e.toString());
	    throw new Error(e);
	}
    }
	
	
    // Equality

    public SPred buildAnyEQ(SAny _arg1, SAny _arg2) {
	Cvc3Any arg1 = (Cvc3Any) _arg1;
	Cvc3Any arg2 = (Cvc3Any) _arg2;
	Cvc3Prover.print("!buildAnyEQ: " + arg1 + " " + arg2);

	try {
	    List key = Arrays.asList(new Object[] { "buildAnyEQ", _arg1, _arg2 });
	    if (escMap.containsKey(key)) {
		return (Cvc3Pred) escMap.get(key);
	    } else {
		Expr e1 = arg1.getExpr();
		Expr e2 = arg2.getExpr();		
		Type t = unify(e1.getType(), e2.getType());
		
		Expr e1c = cast(e1, t);
		Expr e2c = cast(e2, t);
		while (sameCast(e1c, e2c)) {
		    e1c = e1c.getChild(0);
		    e2c = e2c.getChild(0);
		}

		Cvc3Pred node = null;
		boolean rewritten = false;
		if (true || rewrite) {
		    if (e1c.equals(e2c)) {
			//:TODO: move labels
			rewritten = true;
			node = (Cvc3Pred) buildTrue();
		    } else if (rewriteCvc3 && prover.simplify(prover.eqExpr(e1c, e2c)).equals(prover.trueExpr())) {
			rewritten = true;
			assert(rewritten || !prover.simplify(prover.eqExpr(e1c, e2c)).equals(prover.trueExpr()));
			node = (Cvc3Pred) buildTrue();
		    } else if (rewriteCvc3 && prover.simplify(prover.eqExpr(e1c, e2c)).equals(prover.falseExpr())) {
			rewritten = true;
			assert(rewritten || !prover.simplify(prover.eqExpr(e1c, e2c)).equals(prover.falseExpr()));
			node = (Cvc3Pred) buildFalse();
		    }
		}
		if (!rewritten) {
		    node = new Cvc3Pred(prover.eqExpr(e1c, e2c));
		}

		return registerCvc3Pred(key, node);
		
	    }
	} catch (cvc3.Cvc3Exception e) {
	    ErrorSet.fatal(e.toString());
	    throw new Error(e);
	}
    }

    public SPred buildAnyNE(SAny arg1, SAny arg2) {
	Cvc3Prover.print("!buildAnyNE: " + arg1 + " " + arg2);

	return buildNot(buildAnyEQ(arg1, arg2));
    }
	
	
    // Type conversions
    public SValue buildValueConversion(Sort from, Sort to, SValue _value) {
	Cvc3Value value = (Cvc3Value) _value;
	Cvc3Prover.print("!buildValueConversion: " + from + " " + to + " " + value);
	try {
	    List key = Arrays.asList(new Object[] { "buildValueConversion", from, to, value });
	    if (escMap.containsKey(key)) {
		return (Cvc3Value) escMap.get(key);
	    } else {
		Cvc3Value node = (Cvc3Value) wrapExpr(cast(value.getExpr(), to), to);
		escMap.put(key, node);
		return node;
	    }
	} catch (cvc3.Cvc3Exception e) {
	    ErrorSet.fatal(e.toString());
	    throw new Error(e);
	}
    }

    // Type conversions
    public SValue buildPredToBool(SPred _pred) {
	Cvc3Prover.print("!buildPredToBool: " + _pred);
        return buildITE(_pred, buildBool(true), buildBool(false));
    }

    public SPred buildIsTrue(SBool _val) {
	Cvc3Bool val = (Cvc3Bool) _val;
	Cvc3Prover.print("!buildIsTrue: " + val);
	try {
	    List key = Arrays.asList(new Object[] { "buildIsTrue", val });
	    if (escMap.containsKey(key)) {
		return (Cvc3Pred) escMap.get(key);
	    } else {
		Expr e = prover.eqExpr(((Cvc3Bool)buildBool(true)).getExpr(), ((Cvc3Bool)val).getExpr());
		return registerCvc3Pred(key, new Cvc3Pred(e));
	    }
	} catch (cvc3.Cvc3Exception e) {
	    ErrorSet.fatal(e.toString());
	    throw new Error(e);
	}
    }


    // Mobius stuff
    public SPred buildNewObject(SMap oldh, SAny type, SMap heap, SValue r) {
	throw new UnsupportedOperationException();
    }
	
    public SAny buildSort(Sort s) {
	throw new UnsupportedOperationException();
    }
	
    public SValue buildDynSelect(SMap map, SValue obj, SAny field) {
	throw new UnsupportedOperationException();
    }

    public SRef buildDynLoc(SMap map, SValue obj, SAny field) {
	throw new UnsupportedOperationException();
    }
	
    public SMap buildDynStore(SMap map, SValue obj, SAny field, SValue val) {
	throw new UnsupportedOperationException();
    }
	
    public SValue buildArrSelect(SMap map, SRef obj, SInt idx) {
	throw new UnsupportedOperationException();
    }
	
    public SMap buildArrStore(SMap map, SRef obj, SInt idx, SValue val) {
	throw new UnsupportedOperationException();
    }
	
    public SPred buildNewArray(SMap oldh, SAny type, SMap heap, SRef r, SInt len) {
	throw new UnsupportedOperationException();
    }
	
    public SPred buildAssignCompat(SMap map, SValue val, SAny type) {
	throw new UnsupportedOperationException();
    }

    public SPred buildInv(SMap map, SValue val, SAny type) {
	throw new UnsupportedOperationException();
    }

    public SPred buildIsAlive(SMap map, SRef ref) {
	throw new UnsupportedOperationException();
    }

    public SPred buildAssignPred(SMap map, SMap map_pre, SRef target, SRef loc) {
	throw new UnsupportedOperationException();
    }



    //
    // labels
    //

    // from        : if 'from' is a label then move it to wrap 'to'
    // to          : target expression
    // pos         : we are interested in labels of this polarity only
    // flipPolarity: flip the polarity of a label, i.e. when it is moved over a not simplification
    public Cvc3Pred transferLabels(Cvc3Pred from, Cvc3Pred to, boolean flipPolarity) throws Cvc3Exception  {
        // move from to to if from is a label
	if (from instanceof Cvc3Label) {
	    //assert(false);
	    Cvc3Label label = (Cvc3Label) from;
	    //Cvc3Pred transferred = transferLabels(label.getPred(), to, flipPolarity);
	    boolean polarity = label.isPos();
            if (flipPolarity) polarity = !polarity;
            to = (Cvc3Pred) buildLabel(polarity, label.getName(), to);
	}

        // move labels in subexpressions of from to to
        if (from.isLabeled()) {
            if (from.getExpr().isNot()) {
                flipPolarity = !flipPolarity;
            }

            List children = from.getChildren();
            Iterator i = children.iterator();
            while (i.hasNext()) {
                Cvc3Term child = (Cvc3Term) i.next();
                if (child instanceof Cvc3Pred) {
                    transferLabels((Cvc3Pred) child, to, flipPolarity);
                }
            }
        }

        return to;
    }

    public Cvc3Pred transferLabels(Cvc3Pred from, Cvc3Pred to) throws Cvc3Exception  {
        return transferLabels(from, to, false);
    }
}
