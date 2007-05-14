package mobius.directVCGen.formula.coq;

import escjava.sortedProver.EscNodeBuilder;
import escjava.sortedProver.NodeBuilder;
import escjava.sortedProver.Lifter.SortVar;

// TODO: add comments
/*@ non_null_by_default @*/
public class CoqNodeBuilder extends EscNodeBuilder {
	// TODO: add comments
	/*@ non_null_by_default @*/
	public static class CTerm implements STerm, SAny {
		
		// TODO: add comments
		private String rep;
		
		/** tells if the notation is a prefix notation */
		private final boolean prefix;
		
		// TODO: add comments
		protected final STerm [] args;
		
		// TODO: add comments
		public CTerm (boolean prefix, String rep, STerm [] args) {
			this.prefix = prefix;
			this.rep = rep;
			this.args = args;
		}
		
		/*
		 * (non-Javadoc)
		 * @see java.lang.Object#toString()
		 */
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
		
		// TODO: add comments
		public boolean isSubSortOf(Sort s) {
			throw new UnsupportedOperationException("This operation is not used it seems...");
		}
	}
	
	// TODO: add comments
	public class CPred extends CTerm implements SPred {
		// TODO: add comments
		public CPred(boolean pref, String rep, STerm [] args) {
			super(pref, rep, args);
		}
		
		// TODO: add comments
		public CPred(String rep, STerm [] args) {
			super(true, rep, args);
		}
		
		// TODO: add comments
		public CPred(String rep) {
			super(false, rep, new STerm[0]);
		}
		
		// TODO: add comments
		public CPred(boolean b, String rep, STerm t1, STerm t2) {
			this(b, rep, new STerm [] {t1, t2});
		}
	}
	
	// TODO: add comments
	public class CMap extends CTerm implements SMap {
		// TODO: add comments
		public CMap(boolean pref, String rep, STerm [] args) {
			super(pref, rep, args);
		}
		// TODO: add comments
		public CMap(String rep, STerm [] args) {
			super(true, rep, args);
		}
		
		// TODO: add comments
		public CMap(String rep) {
			super(false, rep, new STerm[0]);
		}
	}
	
	// TODO: add comments
	public class CAny extends CTerm implements SMap {
		// TODO: add comments
		public CAny(boolean pref, String rep, STerm [] args) {
			super(pref, rep, args);
		}
		
		// TODO: add comments
		public CAny(String rep, STerm [] args) {
			super(true, rep, args);
		}
		
		// TODO: add comments
		public CAny(String rep) {
			super(false, rep, new STerm[0]);
		}
	}
	
	// TODO: add comments
	public class CType extends CTerm implements SAny {
		// TODO: add comments
		public CType(boolean pref, String rep, STerm [] args) {
			super(pref, rep, args);
		}
		
		// TODO: add comments
		public CType(String rep, STerm [] args) {
			super(true, rep, args);
		}
		
		// TODO: add comments
		public CType(String rep) {
			super(false, rep, new STerm[0]);
		}
		
		// TODO: add comments
		public CType(String rep, STerm h, STerm loc) {
			this(rep, new STerm[] {h, loc});
		}
	}
	
	// TODO: add comments
	public class CForall extends CPred {
		// TODO: add comments
		public final QuantVar[] vars;
		// TODO: add comments
		public CForall(QuantVar[] vars, STerm body) {
			super(false, "forall", new STerm[]{body});
			this.vars = vars;
		}
		
		/*
		 * (non-Javadoc)
		 * @see mobius.directVCGen.formula.coq.CoqNodeBuilder.CTerm#toString()
		 */
		public String toString() {
			String res  = "(forall";
			for(QuantVar v: vars) {
				res += " (" + normalize(v.name) + ":" + buildSort(v.type) + ")";
			}
			res += ", " + args[0] + ")";
			return res;
		}

	}
	
	// TODO: add comments
	public static QuantVar[] removeFirst(QuantVar[] vars) {
		QuantVar[] res = new QuantVar [vars.length - 1];
		for(int i = 1; i < vars.length; i++) {
			res[i -1] = vars[i];
		}
		return res;
	}
	
	// TODO: add comments
	public class CExists extends CForall {
		// TODO: add comments
		public CExists(QuantVar[] vars, STerm body) {
			super(new QuantVar[] {vars[0]}, buildExists(removeFirst(vars), (SPred)body));
		}
		
		/*
		 * (non-Javadoc)
		 * @see mobius.directVCGen.formula.coq.CoqNodeBuilder.CForall#toString()
		 */
		public String toString() {
			String res  = "(exists";
			res +=  normalize(vars[0].name) + ":" + buildSort(vars[0].type);
			res += ", " + args[0] + ")";
			return res;
		}

	}

	// TODO: add comments
	public SAny buildSort(Sort type) {
		if(type instanceof SortVar) {
			type = type.theRealThing();
		}
		if(type.equals(sortPred)) {
			return new CAny("Prop");
		}
		if(type.equals(sortInt)) {
			return new CAny("Int.t");
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
	}
	
	// TODO: add comments
	public class CValue extends CTerm implements SValue {
		// TODO: add comments
		public CValue(boolean pref, String rep, STerm [] args) {
			super(pref, rep, args);
		}
		
		// TODO: add comments
		public CValue(String rep, STerm [] args) {
			super(true, rep, args);
		}
		
		// TODO: add comments
		public CValue(String rep) {
			super(false, rep, new STerm[0]);
		}
		
		// TODO: add comments
		public CValue(String rep, CTerm t) {
			this(rep, new STerm[]{t});
		}
	}
	
	// TODO: add comments
	public class CBool extends CValue implements SBool {
		// TODO: add comments
		public CBool(boolean pref, String rep, STerm [] args) {
			super(pref, rep, args);
		}
		
		// TODO: add comments
		public CBool(String rep, STerm [] args) {
			super(true, rep, args);
		}
		
		// TODO: add comments
		public CBool(String rep) {
			super(false, rep, new STerm[0]);
		}
	}
	
	// TODO: add comments
	public class CInt extends CValue implements SInt {
		// TODO: add comments
		public CInt(boolean pref, String rep, STerm [] args) {
			super(pref, rep, args);
		}
		
		// TODO: add comments
		public CInt(String rep, STerm [] args) {
			super(true, rep, args);
		}
		
		// TODO: add comments
		public CInt(String rep) {
			super(false, rep, new STerm[0]);
		}
		
		// TODO: add comments
		public CInt(String rep, STerm arg) {
			this(rep, new STerm[] {arg});
		}
	}
	
	// TODO: add comments
	public class CReal extends CValue implements SReal {
		// TODO: add comments
		public CReal(boolean pref, String rep, STerm [] args) {
			super(pref, rep, args);
		}
		
		// TODO: add comments
		public CReal(String rep, STerm [] args) {
			super(true, rep, args);
		}
		
		// TODO: add comments
		public CReal(String rep) {
			super(false, rep, new STerm[0]);
		}
	}
	
	// TODO: add comments
	public class CRef extends CValue implements SRef {
		// TODO: add comments
		public CRef(boolean pref, String rep, STerm [] args) {
			super(pref, rep, args);
		}
		
		// TODO: add comments
		public CRef(String rep, STerm [] args) {
			super(true, rep, args);
		}
		
		// TODO: add comments
		public CRef(String rep) {
			super(false, rep, new STerm[0]);
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
		return new CForall(vars, body);
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

	// TODO: add comments
	public static String normalize(String name) {
		if(name.startsWith("#"))
			name = name.substring(1);
		name = name.replace(':', '_');
		name = name.replace('.', '_');
		name = name.replace('\\', '_');
		return name;
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
		return new CExists(vars, body);
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

	// TODO: add comments
	private SRef getLoc(SValue r) {
		return new CRef("loc", new STerm[] {r});
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
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException();
	}

	/*
	 * (non-Javadoc)
	 * @see escjava.sortedProver.NodeBuilder#buildIff(escjava.sortedProver.NodeBuilder.SPred, escjava.sortedProver.NodeBuilder.SPred)
	 */
	@Override
	public SPred buildIff(SPred arg1, SPred arg2) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException();
		
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
		// TODO Auto-generated method stub
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
		// TODO Auto-generated method stub
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
