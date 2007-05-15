package mobius.directVCGen.formula.coq;

import mobius.directVCGen.formula.coq.representation.CBool;
import mobius.directVCGen.formula.coq.representation.CExists;
import mobius.directVCGen.formula.coq.representation.CForall;
import mobius.directVCGen.formula.coq.representation.CInt;
import mobius.directVCGen.formula.coq.representation.CMap;
import mobius.directVCGen.formula.coq.representation.CPred;
import mobius.directVCGen.formula.coq.representation.CReal;
import mobius.directVCGen.formula.coq.representation.CRef;
import mobius.directVCGen.formula.coq.representation.CType;
import mobius.directVCGen.formula.coq.representation.CValue;
import escjava.sortedProver.EscNodeBuilder;
import escjava.sortedProver.NodeBuilder;
import escjava.sortedProver.Lifter.SortVar;

/**
 * The back-end for Coq. Works with bicolano. It does not 
 * work with ESC/Java2 right now because it uses the bicolano
 * memory model which ESC/Java2 doesn't.
 * @author J. Charles
 */
/*@ non_null_by_default @*/
public class CoqNodeBuilder extends EscNodeBuilder {
	/**
	 * Normalize the symbols ... remove from the string
	 * the characters Coq would not like to see
	 * @param name the string to modify
	 * @return the modified string
	 */
	public static String normalize(String name) {
		if(name.startsWith("#"))
			name = name.substring(1);
		name = name.replace(':', '_');
		name = name.replace('.', '_');
		name = name.replace('\\', '_');
		return name;
	}
	
	
	/**
	 * Return the symbol to get a location out of a value
	 * @param r the value to convert
	 * @return a location term
	 */
	public static SRef getLoc(SValue r) {
		return new CRef("loc", new STerm[] {r});
	}
	
	
	/*
	 * (non-Javadoc)
	 * @see escjava.sortedProver.NodeBuilder#buildSort(escjava.sortedProver.NodeBuilder.Sort)
	 */
	public SAny buildSort(Sort type) {
		if(type instanceof SortVar) {
			type = type.theRealThing();
		}
		if(type.equals(sortPred)) {
			return new CType("Prop");
		}
		if(type.equals(sortInt)) {
			return new CType("Int.t");
		}
		if(type.equals(sortReal)) {
			return new CType("Real");
		}
		if(type.equals(sortRef)) {
			return new CType("value");
		}
		if(type.equals(sortBool)) {
			return new CType("bool");
		}
		if(type.equals(sortMap)) {
			return new CType("Heap.t");
		}
		else {
			return new CType("value");
		}
	}
	
	/*
	 * (non-Javadoc)
	 * @see escjava.sortedProver.NodeBuilder#buildAnd(escjava.sortedProver.NodeBuilder.SPred[])
	 */
	@Override
	public SPred buildAnd(SPred[] args) {
		return new CPred(false, "/\\", args);
	}

	/*
	 * (non-Javadoc)
	 * @see escjava.sortedProver.NodeBuilder#buildAnyEQ(escjava.sortedProver.NodeBuilder.SAny, escjava.sortedProver.NodeBuilder.SAny)
	 */
	@Override
	public SPred buildAnyEQ(SAny arg1, SAny arg2) {
		return new CPred(false, "=", new STerm[] {arg1, arg2});
	}

	/*
	 * (non-Javadoc)
	 * @see escjava.sortedProver.NodeBuilder#buildAnyNE(escjava.sortedProver.NodeBuilder.SAny, escjava.sortedProver.NodeBuilder.SAny)
	 */
	@Override
	public SPred buildAnyNE(SAny arg1, SAny arg2) {
		return new CPred(false, "not", new STerm[] {buildAnyEQ(arg1, arg2)});
	}

	/*
	 * (non-Javadoc)
	 * @see escjava.sortedProver.NodeBuilder#buildBool(boolean)
	 */
	@Override
	public SBool buildBool(boolean b) {
		return new CBool(b? "true" : "false");
	}

	/*
	 * (non-Javadoc)
	 * @see escjava.sortedProver.NodeBuilder#buildImplies(escjava.sortedProver.NodeBuilder.SPred, escjava.sortedProver.NodeBuilder.SPred)
	 */
	@Override
	public SPred buildImplies(SPred arg1, SPred arg2) {
		return new CPred(false, "->", new STerm [] {arg1, arg2});
	}
	
	@Override
	public SPred buildForAll(QuantVar[] vars, SPred body, STerm[][] pats, STerm[] nopats) {
		return new CForall(this, vars, body);
	}
	
	/*
	 * (non-Javadoc)
	 * @see escjava.sortedProver.NodeBuilder#buildQVarRef(escjava.sortedProver.NodeBuilder.QuantVar)
	 */
	@Override
	public SAny buildQVarRef(QuantVar v) {
		String name = normalize(v.name);
		Sort s = v.type;
		if(s instanceof SortVar) {
			s = s.theRealThing();
		}
		
		if (s.equals(sortBool)) {
			return new CBool(name);
		}
		else if (s.equals(sortRef)) {
			return new CRef(name);
		}
		else if (s.equals(sortInt)) {
			return new CInt(name);
		}
		else if (s.equals(sortReal)) {
			return new CReal(name);
		}
		else if (s.equals(sortMap)) {
			return new CMap(name);
		}
		else if (s.equals(sortAny)) {
			throw new IllegalArgumentException("The type of " + v + "should not be any, it should be known!");
		}
		else if (s.equals(sortPred)) {
			throw new IllegalArgumentException("The type should not be pred!");
		}
		else
			throw new IllegalArgumentException("Unknown Type: " + s.getClass() + " " + sortRef.getClass());
	}



	/*
	 * (non-Javadoc)
	 * @see escjava.sortedProver.NodeBuilder#buildInt(long)
	 */
	@Override
	public SInt buildInt(long n) {
		return new CInt("Int.const", new STerm[]{new CInt(""+ n)});
	}

	/*
	 * (non-Javadoc)
	 * @see escjava.sortedProver.NodeBuilder#buildIntBoolFun(int, escjava.sortedProver.NodeBuilder.SInt, escjava.sortedProver.NodeBuilder.SInt)
	 */
	@Override
	public SBool buildIntBoolFun(int tag, SInt arg1, SInt arg2) {
		switch (tag) {
			case predEQ:
				return new CBool("eq_bool", new STerm[]{arg1, arg2});
			case predLT:
				return new CBool("lt_bool", new STerm[]{arg1, arg2});
			case predLE:
				return new CBool("le_bool", new STerm[]{arg1, arg2});

			case predGT:	
			case predGE:
				throw new UnsupportedOperationException("Constructs gt or ge should"
						+ " be desugared to lt and le...");
			default:
				throw new IllegalArgumentException("Unknown tag " + tag);
				
		}
	}
	
	/*
	 * (non-Javadoc)
	 * @see escjava.sortedProver.NodeBuilder#buildIsTrue(escjava.sortedProver.NodeBuilder.SBool)
	 */
	@Override
	public SPred buildIsTrue(SBool val) {
		return new CPred("Is_true", new STerm[] {val});
	}

	/*
	 * (non-Javadoc)
	 * @see escjava.sortedProver.NodeBuilder#buildDistinct(escjava.sortedProver.NodeBuilder.SAny[])
	 */
	@Override
	public SPred buildDistinct(SAny[] terms) {
		throw new UnsupportedOperationException("Distinct elements don't mean anything for Coq!");
	}
	
	
	/*
	 * (non-Javadoc)
	 * @see escjava.sortedProver.NodeBuilder#buildExists(escjava.sortedProver.NodeBuilder.QuantVar[], escjava.sortedProver.NodeBuilder.SPred)
	 */
	@Override
	public SPred buildExists(QuantVar[] vars, SPred body) {
		if(vars.length == 0)
			return body;
		return new CExists(this, vars, body);
	}

	/*
	 * (non-Javadoc)
	 * @see escjava.sortedProver.NodeBuilder#buildNull()
	 */
	@Override
	public SRef buildNull() {
		return new CRef("Null");
	}
	
	/*
	 * (non-Javadoc)
	 * @see escjava.sortedProver.NodeBuilder#buildITE(escjava.sortedProver.NodeBuilder.SPred, escjava.sortedProver.NodeBuilder.SValue, escjava.sortedProver.NodeBuilder.SValue)
	 */
	@Override
	public SValue buildITE(SPred cond, SValue then_part, SValue else_part) {
		// should not appear in this form ... the typing is a bit loosy
		throw new UnsupportedOperationException("I don't like this construct, get rid of it!");
	}
	
	/*
	 * (non-Javadoc)
	 * @see escjava.sortedProver.NodeBuilder#buildNot(escjava.sortedProver.NodeBuilder.SPred)
	 */
	@Override
	public SPred buildNot(SPred arg) {
		return new CPred("not", new STerm[] {arg});
	}
	
	/*
	 * (non-Javadoc)
	 * @see escjava.sortedProver.NodeBuilder#buildTrue()
	 */
	@Override
	public SPred buildTrue() {
		return new CPred("True");
	}
	
	/*
	 * (non-Javadoc)
	 * @see escjava.sortedProver.NodeBuilder#buildReal(double)
	 */
	@Override
	public SReal buildReal(double f) {
		throw new UnsupportedOperationException("Translation of reals is not supported yet!");
	}

	/*
	 * (non-Javadoc)
	 * @see escjava.sortedProver.NodeBuilder#buildRealBoolFun(int, escjava.sortedProver.NodeBuilder.SReal, escjava.sortedProver.NodeBuilder.SReal)
	 */
	@Override
	public SBool buildRealBoolFun(int realPredTag, SReal arg1, SReal arg2) {
		throw new UnsupportedOperationException("Translation of reals is not supported yet!");
	}

	/*
	 * (non-Javadoc)
	 * @see escjava.sortedProver.NodeBuilder#buildRealFun(int, escjava.sortedProver.NodeBuilder.SReal, escjava.sortedProver.NodeBuilder.SReal)
	 */
	@Override
	public SReal buildRealFun(int realFunTag, SReal arg1, SReal arg2) {
		throw new UnsupportedOperationException("Translation of reals is not supported yet!");
	}

	/*
	 * (non-Javadoc)
	 * @see escjava.sortedProver.NodeBuilder#buildRealFun(int, escjava.sortedProver.NodeBuilder.SReal)
	 */
	@Override
	public SReal buildRealFun(int realFunTag, SReal arg1) {
		throw new UnsupportedOperationException("Translation of reals is not supported yet!");
	}

	/*
	 * (non-Javadoc)
	 * @see escjava.sortedProver.NodeBuilder#buildRealPred(int, escjava.sortedProver.NodeBuilder.SReal, escjava.sortedProver.NodeBuilder.SReal)
	 */
	@Override
	public SPred buildRealPred(int realPredTag, SReal arg1, SReal arg2) {
		throw new UnsupportedOperationException("Translation of reals is not supported yet!");
	}

	/*
	 * (non-Javadoc)
	 * @see escjava.sortedProver.NodeBuilder#buildOr(escjava.sortedProver.NodeBuilder.SPred[])
	 */
	@Override
	public SPred buildOr(SPred[] args) {
		return new CPred(false, "\\/", args);
	}
	
	/*
	 * (non-Javadoc)
	 * @see escjava.sortedProver.NodeBuilder#buildPredCall(escjava.sortedProver.NodeBuilder.PredSymbol, escjava.sortedProver.NodeBuilder.SAny[])
	 */
	@Override
	public SPred buildPredCall(PredSymbol fn, SAny[] args) {
		if(fn == symRefEQ) {
			return new CPred(false, "=", args);
		}
		if(fn == symRefNE) {
			return this.buildNot(new CPred(false, "=", args));
		}
		if(fn == symTypeLE) {
			SAny [] realargs = {new CMap("p"),
									args[0], args[1]};
			return new CPred("subclass_name", realargs);
		}
		else {
			return new CPred(fn.name, args);
		}
		//throw new IllegalArgumentException("Unknown symbol: " + fn);
	}
	
	/*
	 * (non-Javadoc)
	 * @see escjava.sortedProver.NodeBuilder#buildFnCall(escjava.sortedProver.NodeBuilder.FnSymbol, escjava.sortedProver.NodeBuilder.SAny[])
	 */
	@Override
	public SAny buildFnCall(FnSymbol fn, SAny[] args) {
		if(fn.equals(symTypeOf)) {
			if(args.length == 2) {
				return new CType("typeof", args[0], getLoc((SValue)args[1]));
			}
		}
		throw new IllegalArgumentException("Unknown symbol: " + fn);
	}

	/*
	 * (non-Javadoc)
	 * @see escjava.sortedProver.NodeBuilder#buildLabel(boolean, java.lang.String, escjava.sortedProver.NodeBuilder.SPred)
	 */
	@Override
	public SPred buildLabel(boolean positive, String name, SPred pred) {
		throw new UnsupportedOperationException("Labels have no real meanings for us, right?");
	}
	
	/*
	 * (non-Javadoc)
	 * @see escjava.sortedProver.NodeBuilder#buildValueConversion(escjava.sortedProver.NodeBuilder.Sort, escjava.sortedProver.NodeBuilder.Sort, escjava.sortedProver.NodeBuilder.SValue)
	 */
	@Override
	public SValue buildValueConversion(Sort from, Sort to, SValue val) {
		if(from == sortValue) {
			if(to == sortRef) {
				return val;
			}
			else if(to == sortBool) {
				return new CBool("vBool", new STerm[] {val});
			}
			else if(to == sortInt) {
				return new CInt("vInt", new STerm[] {val});
			}
			else if(to == sortReal) {
				throw new UnsupportedOperationException("We do not support reals right now...");
			}
			else 
				throw new IllegalArgumentException("The conversion can only be done from a value to a simple type. Found:" + to);
			
		}
		else {
			if (to != sortValue) {
				throw new IllegalArgumentException("The conversion can only be done from a simple type to a value. Found:" + to);
			}
			if(from == sortRef) {
				return val;
			}
			else if(from == sortBool) {
				return new CValue("Num", new CInt("B ", new STerm[] {val}));
			}
			else if(from == sortInt) {
				return new CValue("Num", new CInt("I ", new STerm[] {val}));
			}
			else if(from == sortReal) {
				throw new UnsupportedOperationException("We do not support reals right now...");
			}
			else 
				throw new IllegalArgumentException("The conversion can only be done from a value to a simple type. Found:" + to);
			
		}
	}

	

	/*
	 * (non-Javadoc)
	 * @see escjava.sortedProver.NodeBuilder#buildNewObject(escjava.sortedProver.NodeBuilder.SMap, escjava.sortedProver.NodeBuilder.SAny, escjava.sortedProver.NodeBuilder.SMap, escjava.sortedProver.NodeBuilder.SRef)
	 */
	@Override
	public SPred buildNewObject(SMap oldh, SAny type, SMap heap, SRef r) {
		CPred left = new CPred("Heap.new", new STerm[] {oldh, new CMap("p"), new CType("Heap.LocationObject", new STerm[] {type})});
        CPred right = new CPred("Some", new STerm[] {new CPred(false, ",", new STerm[] {getLoc(r), heap})});
    		
		SPred res = new CPred(false, "=",new STerm[] {left, right});
		return res;
	}
	
	/*
	 * (non-Javadoc)
	 * @see escjava.sortedProver.NodeBuilder#buildSelect(escjava.sortedProver.NodeBuilder.SMap, escjava.sortedProver.NodeBuilder.SValue)
	 */
	@Override
	public SValue buildSelect(SMap map, SValue idx) {		
		CRef addr = new CRef("Heap.StaticField", new STerm [] {idx});
		return new CValue("get", new STerm[] {map, addr});
	}
	
	/*
	 * (non-Javadoc)
	 * @see escjava.sortedProver.NodeBuilder#buildStore(escjava.sortedProver.NodeBuilder.SMap, escjava.sortedProver.NodeBuilder.SValue, escjava.sortedProver.NodeBuilder.SValue)
	 */
	@Override
	public SMap buildStore(SMap map, SValue idx, SValue val) {
		CRef addr = new CRef("Heap.StaticField", new STerm [] {idx});
		return new CMap("Heap.update", new STerm[] {map, addr, val});
	}
	
	
	/*
	 * (non-Javadoc)
	 * @see escjava.sortedProver.NodeBuilder#buildDynSelect(escjava.sortedProver.NodeBuilder.SMap, escjava.sortedProver.NodeBuilder.SRef, escjava.sortedProver.NodeBuilder.SAny)
	 */
	@Override
	public SValue buildDynSelect(SMap heap, SRef obj, SAny field) {
		CRef addr = new CRef("Heap.DynamicField", new STerm [] {getLoc(obj), field});
		return new CValue("get", new STerm[] {heap, addr});
	}

	/*
	 * (non-Javadoc)
	 * @see escjava.sortedProver.NodeBuilder#buildDynStore(escjava.sortedProver.NodeBuilder.SMap, escjava.sortedProver.NodeBuilder.SRef, escjava.sortedProver.NodeBuilder.SAny, escjava.sortedProver.NodeBuilder.SValue)
	 */
	@Override
	public SMap buildDynStore(SMap map, SRef obj, SAny field, SValue val) {
		CRef addr = new CRef("Heap.DynamicField", new STerm [] {getLoc(obj), field});
		return new CMap("Heap.update", new STerm[] {map, addr, val});
		
	}

	/*
	 * (non-Javadoc)
	 * @see escjava.sortedProver.NodeBuilder#buildArrSelect(escjava.sortedProver.NodeBuilder.SMap, escjava.sortedProver.NodeBuilder.SRef, escjava.sortedProver.NodeBuilder.SInt)
	 */
	@Override
	public SValue buildArrSelect(SMap heap, SRef obj, SInt idx) {
		CRef addr = new CRef("Heap.ArrayElement", new STerm [] {getLoc(obj), idx});
		return new CValue("get", new STerm[] {heap, addr});
	}

	/*
	 * (non-Javadoc)
	 * @see escjava.sortedProver.NodeBuilder#buildArrStore(escjava.sortedProver.NodeBuilder.SMap, escjava.sortedProver.NodeBuilder.SRef, escjava.sortedProver.NodeBuilder.SInt, escjava.sortedProver.NodeBuilder.SValue)
	 */
	@Override
	public SMap buildArrStore(SMap map, SRef obj, SInt idx, SValue val) {
		CRef addr = new CRef("Heap.ArrayElement", new STerm [] {getLoc(obj), idx});
		return new CMap("Heap.update", new STerm[] {map, addr, val});
	}

	/*
	 * (non-Javadoc)
	 * @see escjava.sortedProver.NodeBuilder#buildNewArray(escjava.sortedProver.NodeBuilder.SMap, escjava.sortedProver.NodeBuilder.SAny, escjava.sortedProver.NodeBuilder.SMap, escjava.sortedProver.NodeBuilder.SRef, escjava.sortedProver.NodeBuilder.SInt)
	 */
	@Override
	public SPred buildNewArray(SMap oldh, SAny type, SMap heap, SRef r, SInt len) {
		CPred left = new CPred("Heap.new", new STerm[] {oldh, new CMap("p"), new CType("Heap.LocationArray", new STerm[] {len, type})});
        CPred right = new CPred("Some", new STerm[] {new CPred(false, ",", new STerm[] {getLoc(r), heap})});
    		
		SPred res = new CPred(false, "=",new STerm[] {left, right});
		return res;
	}

	/*
	 * (non-Javadoc)
	 * @see escjava.sortedProver.NodeBuilder#buildConstantRef(escjava.sortedProver.NodeBuilder.FnSymbol)
	 */
	@Override
	public SAny buildConstantRef(FnSymbol c) {
		throw new UnsupportedOperationException();
	}

	/*
	 * (non-Javadoc)
	 * @see escjava.sortedProver.NodeBuilder#buildIff(escjava.sortedProver.NodeBuilder.SPred, escjava.sortedProver.NodeBuilder.SPred)
	 */
	@Override
	public SPred buildIff(SPred arg1, SPred arg2) {
		return new CPred(false, "<->", new STerm [] {arg1, arg2});
	}

	/*
	 * (non-Javadoc)
	 * @see escjava.sortedProver.NodeBuilder#buildIntFun(int, escjava.sortedProver.NodeBuilder.SInt, escjava.sortedProver.NodeBuilder.SInt)
	 */
	@Override
	public SInt buildIntFun(int intFunTag, SInt arg1, SInt arg2) {
		switch (intFunTag) {
		case NodeBuilder.funADD:
			return new CInt("Int.add", new STerm[] {arg1, arg2});
		}
		throw new UnsupportedOperationException("Cannot translate the tag: "
				+ NodeBuilder.tagsIds[intFunTag]);

	}

	/*
	 * (non-Javadoc)
	 * @see escjava.sortedProver.NodeBuilder#buildIntFun(int, escjava.sortedProver.NodeBuilder.SInt)
	 */
	@Override
	public SInt buildIntFun(int intFunTag, SInt arg1) {
		throw new UnsupportedOperationException();
	}

	/*
	 * (non-Javadoc)
	 * @see escjava.sortedProver.NodeBuilder#buildIntPred(int, escjava.sortedProver.NodeBuilder.SInt, escjava.sortedProver.NodeBuilder.SInt)
	 */
	@Override
	public SPred buildIntPred(int intPredTag, SInt arg1, SInt arg2) {
		switch (intPredTag) {
			case NodeBuilder.predLE:
				return new CPred(false, "<", new CInt("Int.toZ", arg1),
											new CInt("Int.toZ", arg2));
			case NodeBuilder.predLT:
				return new CPred(false, "<=", new CInt("Int.toZ", arg1),
						new CInt("Int.toZ", arg2));
			case NodeBuilder.predEQ:
				return new CPred(false, "=", new CInt("Int.toZ", arg1),
						new CInt("Int.toZ", arg2));
		}
		throw new UnsupportedOperationException(NodeBuilder.tagsIds[intPredTag]);
	}

	/*
	 * (non-Javadoc)
	 * @see escjava.sortedProver.NodeBuilder#buildXor(escjava.sortedProver.NodeBuilder.SPred, escjava.sortedProver.NodeBuilder.SPred)
	 */
	@Override
	public SPred buildXor(SPred arg1, SPred arg2) {
		throw new UnsupportedOperationException();
	}

	/*
	 * (non-Javadoc)
	 * @see escjava.sortedProver.NodeBuilder#buildAssignCompat(escjava.sortedProver.NodeBuilder.SMap, escjava.sortedProver.NodeBuilder.SValue, escjava.sortedProver.NodeBuilder.SAny)
	 */
	@Override
	public SPred buildAssignCompat(SMap map, SValue val, SAny type) {
		return new CPred("assign_compatible", new STerm [] {new CMap("p"), map, val, type});
	}

	
}
