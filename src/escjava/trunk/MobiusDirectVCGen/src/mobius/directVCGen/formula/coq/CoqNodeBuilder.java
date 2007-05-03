package mobius.directVCGen.formula.coq;

import mobius.directVCGen.formula.Formula;
import escjava.sortedProver.EscNodeBuilder;
import escjava.sortedProver.Lifter.SortVar;
import escjava.sortedProver.NodeBuilder.SAny;

/*@ non_null_by_default @*/
public class CoqNodeBuilder extends EscNodeBuilder {
	/*@ non_null_by_default @*/
	public static class CTerm implements STerm, SAny {
		
		private String rep;
		/** tells if the notation is a prefix notation */
		private final boolean prefix;
		protected final STerm [] args;
		
		public CTerm (boolean prefix, String rep, STerm [] args) {
			this.prefix = prefix;
			this.rep = rep;
			this.args = args;
		}
		
		public String toString() {
			String res = "";
			if (args.length == 0) {
				return rep;
			} 
			else if(args.length == 1) {
				if(prefix) {
					res = "(" + rep + " " + args[0] + ")";
				}
				else {
					res = "(" + args[0] + " " + rep + ")";
				}
			}
			else {
				if ((!prefix) && (args.length == 2)) {
					
						res = "(" + args[0] + " " + rep + " " + args[1] + ")";
				}
				else {
					res = "(" + rep;
					for (STerm t: args) {
						res += " " + t;
					}
					res += ")";
				}
			}
			return res;
		}
		public boolean isSubSortOf(Sort s) {
			throw new UnsupportedOperationException("This operation is not used it seems...");
		}
	}
	
	public class CPred extends CTerm implements SPred {

		public CPred(boolean pref, String rep, STerm [] args) {
			super(pref, rep, args);
		}
		public CPred(String rep, STerm [] args) {
			super(true, rep, args);
		}
		
		public CPred(String rep) {
			super(false, rep, new STerm[0]);
		}
	}
	public class CMap extends CTerm implements SMap {

		public CMap(boolean pref, String rep, STerm [] args) {
			super(pref, rep, args);
		}
		public CMap(String rep, STerm [] args) {
			super(true, rep, args);
		}
		
		public CMap(String rep) {
			super(false, rep, new STerm[0]);
		}
	}
	public class CAny extends CTerm implements SMap {

		public CAny(boolean pref, String rep, STerm [] args) {
			super(pref, rep, args);
		}
		public CAny(String rep, STerm [] args) {
			super(true, rep, args);
		}
		
		public CAny(String rep) {
			super(false, rep, new STerm[0]);
		}
	}
	public class CType extends CTerm implements SAny {

		public CType(boolean pref, String rep, STerm [] args) {
			super(pref, rep, args);
		}
		public CType(String rep, STerm [] args) {
			super(true, rep, args);
		}
		
		public CType(String rep) {
			super(false, rep, new STerm[0]);
		}
	}
	public class CForall extends CPred {
		public final QuantVar[] vars;
		public CForall(QuantVar[] vars, STerm body) {
			super(false, "forall", new STerm[]{body});
			this.vars = vars;
		}
		
		public String toString() {
			String res  = "(forall";
			for(QuantVar v: vars) {
				res += " (" + normalize(v.name) + ":" + buildSort(v.type) + ")";
			}
			res += ", " + args[0] + ")";
			return res;
		}

	}
	public static QuantVar[] removeFirst(QuantVar[] vars) {
		QuantVar[] res = new QuantVar [vars.length - 1];
		for(int i = 1; i < vars.length; i++) {
			res[i -1] = vars[i];
		}
		return res;
	}
	public class CExists extends CForall {

		public CExists(QuantVar[] vars, STerm body) {
			super(new QuantVar[] {vars[0]}, buildExists(removeFirst(vars), (SPred)body));
		}
		


		public String toString() {
			String res  = "(exists";
			res +=  normalize(vars[0].name) + ":" + buildSort(vars[0].type);
			res += ", " + args[0] + ")";
			return res;
		}

	}


	public SAny buildSort(Sort type) {
		if(type instanceof SortVar) {
			type = type.theRealThing();
		}
		if(type.equals(sortPred)) {
			return new CAny("Prop");
		}
		if(type.equals(sortInt)) {
			return new CAny("Z");
		}
		if(type.equals(sortReal)) {
			return new CAny("Real");
		}
		if(type.equals(sortRef)) {
			return new CAny("value");
		}
		if(type.equals(sortBool)) {
			return new CAny("bool");
		}
		if(type.equals(sortMap)) {
			return new CAny("Heap.t");
		}
		else {
			return new CAny("value");
		}
		//throw new IllegalArgumentException("Unknown sort: " + type + " " + type.getClass());
	}
	
	
	public class CValue extends CTerm implements SValue {

		public CValue(boolean pref, String rep, STerm [] args) {
			super(pref, rep, args);
		}
		public CValue(String rep, STerm [] args) {
			super(true, rep, args);
		}
		
		public CValue(String rep) {
			super(false, rep, new STerm[0]);
		}
	}
	public class CBool extends CValue implements SBool {
		public CBool(boolean pref, String rep, STerm [] args) {
			super(pref, rep, args);
		}
		public CBool(String rep, STerm [] args) {
			super(true, rep, args);
		}
		
		public CBool(String rep) {
			super(false, rep, new STerm[0]);
		}
	}
	public class CInt extends CValue implements SInt {
		public CInt(boolean pref, String rep, STerm [] args) {
			super(pref, rep, args);
		}
		public CInt(String rep, STerm [] args) {
			super(true, rep, args);
		}
		
		public CInt(String rep) {
			super(false, rep, new STerm[0]);
		}
	}
	public class CReal extends CValue implements SReal {
		public CReal(boolean pref, String rep, STerm [] args) {
			super(pref, rep, args);
		}
		public CReal(String rep, STerm [] args) {
			super(true, rep, args);
		}
		
		public CReal(String rep) {
			super(false, rep, new STerm[0]);
		}
	}
	public class CRef extends CValue implements SRef {
		public CRef(boolean pref, String rep, STerm [] args) {
			super(pref, rep, args);
		}
		public CRef(String rep, STerm [] args) {
			super(true, rep, args);
		}
		
		public CRef(String rep) {
			super(false, rep, new STerm[0]);
		}
	}
	
	
	@Override
	public SPred buildAnd(SPred[] args) {
		return new CPred(false, "/\\", args);
	}

	@Override
	public SPred buildAnyEQ(SAny arg1, SAny arg2) {
		
		return new CPred(false, "=", new STerm[] {arg1, arg2});
	}

	@Override
	public SPred buildAnyNE(SAny arg1, SAny arg2) {
		return new CPred(false, "not", new STerm[] {buildAnyEQ(arg1, arg2)});
	}

	@Override
	public SBool buildBool(boolean b) {
		return new CBool(b? "true" : "false");
	}

	@Override
	public SPred buildImplies(SPred arg1, SPred arg2) {
		return new CPred(false, "->", new STerm [] {arg1, arg2});
	}
	
	@Override
	public SPred buildForAll(QuantVar[] vars, SPred body, STerm[][] pats, STerm[] nopats) {
		return new CForall(vars, body);
	}
	
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
		else if (s.equals(sortPred)) {
			return new CPred(name);
		}
		else if (s.equals(sortMap)) {
			return new CMap(name);
		}
		else if (s.equals(sortAny)) {
			return new CAny(name);
		}
		else
			throw new IllegalArgumentException("Unknown Type: " + s.getClass() + " " + sortRef.getClass());
	}

	public static String normalize(String name) {
		if(name.startsWith("#"))
			name = name.substring(1);
		name = name.replace(':', '_');
		name = name.replace('.', '_');
		name = name.replace('\\', '_');
		return name;
	}

	@Override
	public SInt buildInt(long n) {
		return new CInt("" + n);
	}

	@Override
	public SBool buildIntBoolFun(int tag, SInt arg1, SInt arg2) {
		switch (tag) {
			case predEQ:
				return new CBool("Zeq_bool", new STerm[]{arg1, arg2});
			case predLT:
				return new CBool("Zlt_bool", new STerm[]{arg1, arg2});
			case predLE:
				return new CBool("Zle_bool", new STerm[]{arg1, arg2});

			case predGT:	
			case predGE:
				throw new UnsupportedOperationException("Constructs gt or ge should"
						+ " be desugared to lt and le...");
			default:
				throw new IllegalArgumentException("Unknown tag " + tag);
				
		}
	}
	@Override
	public SPred buildIsTrue(SBool val) {
		return new CPred("Is_true", new STerm[] {val});
	}

	@Override
	public SPred buildDistinct(SAny[] terms) {
		throw new UnsupportedOperationException("Distinct elements don't mean anything for Coq!");
	}
	
	@Override
	public SPred buildExists(QuantVar[] vars, SPred body) {
		if(vars.length == 0)
			return body;
		return new CExists(vars, body);
	}

	@Override
	public SRef buildNull() {
		return new CRef("Null");
	}
	
	@Override
	public SValue buildITE(SPred cond, SValue then_part, SValue else_part) {
		// should not appear in this form ... the typing is a bit loosy
		throw new UnsupportedOperationException("I don't like this construct, get rid of it!");
	}
	@Override
	public SPred buildNot(SPred arg) {
		return new CPred("not", new STerm[] {arg});
	}
	
	@Override
	public SPred buildTrue() {
		return new CPred("True");
	}
	
	@Override
	public SReal buildReal(double f) {
		throw new UnsupportedOperationException("Translation of reals is not supported yet!");
	}

	@Override
	public SBool buildRealBoolFun(int realPredTag, SReal arg1, SReal arg2) {
		throw new UnsupportedOperationException("Translation of reals is not supported yet!");
	}

	@Override
	public SReal buildRealFun(int realFunTag, SReal arg1, SReal arg2) {
		throw new UnsupportedOperationException("Translation of reals is not supported yet!");
	}

	@Override
	public SReal buildRealFun(int realFunTag, SReal arg1) {
		throw new UnsupportedOperationException("Translation of reals is not supported yet!");
	}

	@Override
	public SPred buildRealPred(int realPredTag, SReal arg1, SReal arg2) {
		throw new UnsupportedOperationException("Translation of reals is not supported yet!");
	}

	@Override
	public SPred buildOr(SPred[] args) {
		return new CPred(false, "\\/", args);
	}
	
	@Override
	public SPred buildPredCall(PredSymbol fn, SAny[] args) {
		if(fn == symRefEQ) {
			return new CPred(false, "=", args);
		}
		if(fn == symRefNE) {
			return this.buildNot(new CPred(false, "=", args));
		}
		if(fn == symTypeLE) {
			SAny [] realargs = {buildQVarRef(Formula.program.qvar),
									args[0], args[1]};
			return new CPred("subclass_name", realargs);
		}
		else {
			return new CPred(fn.name, args);
		}
		//throw new IllegalArgumentException("Unknown symbol: " + fn);
	}
	
	@Override
	public SAny buildFnCall(FnSymbol fn, SAny[] args) {
		if(fn.equals(symTypeOf)) {
			if(args.length == 2) {
				return new CType("typeof", args);
			}
		}
		throw new IllegalArgumentException("Unknown symbol: " + fn);
	}

	@Override
	public SPred buildLabel(boolean positive, String name, SPred pred) {
		throw new UnsupportedOperationException("Labels have no real meanings for us, right?");
	}
	
	

	


	@Override
	public SValue buildValueConversion(Sort from, Sort to, SValue val) {
		if(from == sortValue) {
			if(to == sortRef) {
				return new CValue("vRef", new STerm[] {val});
			}
			else if(to == sortBool) {
				return new CValue("vBool", new STerm[] {val});
			}
			else if(to == sortInt) {
				return new CValue("vInt", new STerm[] {val});
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
				return new CRef("rValue", new STerm[] {val});
			}
			else if(from == sortBool) {
				return new CBool("bValue", new STerm[] {val});
			}
			else if(from == sortInt) {
				return new CInt("iValue", new STerm[] {val});
			}
			else if(from == sortReal) {
				throw new UnsupportedOperationException("We do not support reals right now...");
			}
			else 
				throw new IllegalArgumentException("The conversion can only be done from a value to a simple type. Found:" + to);
			
		}
	}

	private SRef getLoc(SValue r) {
		return new CRef("loc", new STerm[] {r});
	}


	@Override
	public SPred buildNewObject(SMap oldh, SAny type, SMap heap, SRef r) {
		CPred left = new CPred("Heap.new", new STerm[] {oldh, buildQVarRef(Formula.program.qvar), new CType("Heap.LocationObject", new STerm[] {type})});
        CPred right = new CPred("Some", new STerm[] {new CPred(false, ",", new STerm[] {getLoc(r), heap})});
    		
		SPred res = new CPred(false, "=",new STerm[] {left, right});
		return res;
	}
	@Override
	public SValue buildSelect(SMap map, SValue idx) {		
		CRef addr = new CRef("Heap.StaticField", new STerm [] {idx});
		return new CValue("Heap.get", new STerm[] {map, addr});
	}
	@Override
	public SMap buildStore(SMap map, SValue idx, SValue val) {
		CRef addr = new CRef("Heap.StaticField", new STerm [] {idx});
		return new CMap("Heap.update", new STerm[] {map, addr, val});
	}
	
	@Override
	public SValue buildDynSelect(SMap heap, SRef obj, SAny field) {
		CRef addr = new CRef("Heap.DynamicField", new STerm [] {getLoc(obj), field});
		return new CValue("Heap.get", new STerm[] {heap, addr});
	}

	@Override
	public SMap buildDynStore(SMap map, SRef obj, SAny field, SValue val) {
		CRef addr = new CRef("Heap.DynamicField", new STerm [] {getLoc(obj), field});
		return new CMap("Heap.update", new STerm[] {map, addr, val});
		
	}

	@Override
	public SValue buildArrSelect(SMap map, SRef obj, SInt idx) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public SMap buildArrStore(SMap map, SRef obj, SInt idx, SValue val) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public SPred buildNewArray(SMap oldh, SAny type, SMap heap, SRef r, SInt len) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public SAny buildConstantRef(FnSymbol c) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException();
	}

	@Override
	public SPred buildIff(SPred arg1, SPred arg2) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException();
		
	}

	@Override
	public SInt buildIntFun(int intFunTag, SInt arg1, SInt arg2) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException();

	}

	@Override
	public SInt buildIntFun(int intFunTag, SInt arg1) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException();
	}

	@Override
	public SPred buildIntPred(int intPredTag, SInt arg1, SInt arg2) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException();
	}

	
	@Override
	public SPred buildXor(SPred arg1, SPred arg2) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException();
	}

	
}
