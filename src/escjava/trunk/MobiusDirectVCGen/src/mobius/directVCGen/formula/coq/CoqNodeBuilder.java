package mobius.directVCGen.formula.coq;

import mobius.directVCGen.formula.Logic;
import mobius.directVCGen.formula.Num;
import mobius.directVCGen.formula.Ref;
import escjava.sortedProver.EscNodeBuilder;
import escjava.sortedProver.Lifter.QuantVariable;

/*@ non_null_by_default @*/
public class CoqNodeBuilder extends EscNodeBuilder {
	/*@ non_null_by_default @*/
	public static class CTerm implements STerm, SAny {
		
		private String rep;
		/** tells if the notation is a prefix notation */
		private final boolean prefix;
		private final STerm [] args;
		
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
			if(args.length == 1) {
				if(prefix) {
					res = "(" + args[0] + " " + rep + ")";
				}
				else {
					res = "(" + rep + " " + args[0] + ")";
				}
			}
			if(args.length == 2) {
				if (!prefix) {
					res = "(" + args[0] + " " + rep + " " + args[1] + ")";
				}
			}
			else {
				res = "(" + rep;
				for (STerm t: args) {
					res += " " + t;
				}
				res += ")";
			}
			return res;
		}
		public boolean isSubSortOf(Sort s) {
			// TODO: understand the use of that
			return false;
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
	public SAny buildConstantRef(FnSymbol c) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public SPred buildDistinct(SAny[] terms) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public SPred buildExists(QuantVar[] vars, SPred body) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public SAny buildFnCall(FnSymbol fn, SAny[] args) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public SPred buildForAll(QuantVar[] vars, SPred body, STerm[][] pats, STerm[] nopats) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public SValue buildITE(SPred cond, SValue then_part, SValue else_part) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public SPred buildIff(SPred arg1, SPred arg2) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public SPred buildImplies(SPred arg1, SPred arg2) {
		return new CPred(false, "->", new STerm [] {arg1, arg2});
	}

	@Override
	public SInt buildInt(long n) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public SBool buildIntBoolFun(int tag, SInt arg1, SInt arg2) {
		switch (tag) {
			case predEQ:
				break;
			case predGT:
				break;	
			case predGE:
				break;
				
		}
		return null;
	}

	@Override
	public SInt buildIntFun(int intFunTag, SInt arg1, SInt arg2) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public SInt buildIntFun(int intFunTag, SInt arg1) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public SPred buildIntPred(int intPredTag, SInt arg1, SInt arg2) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public SPred buildIsTrue(SBool val) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public SPred buildLabel(boolean positive, String name, SPred pred) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public SPred buildNot(SPred arg) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public SRef buildNull() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public SPred buildOr(SPred[] args) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public SPred buildPredCall(PredSymbol fn, SAny[] args) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public SAny buildQVarRef(QuantVariable v) {
		if (v.type == sortBool) {
			return new CBool(v.name);
		}
		else if (v.type == Ref.sort) {
			return new CRef(v.name);
		}
		else if (v.type == Num.sortInt) {
			return new CInt(v.name);
		}
		else if (v.type == Num.sortReal) {
			return new CReal(v.name);
		}
		else if (v.type == Logic.sort) {
			return new CPred(v.name);
		}
		else
			throw new IllegalArgumentException("Unknown Type: " + v.type);
	}

	@Override
	public SReal buildReal(double f) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public SBool buildRealBoolFun(int realPredTag, SReal arg1, SReal arg2) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public SReal buildRealFun(int realFunTag, SReal arg1, SReal arg2) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public SReal buildRealFun(int realFunTag, SReal arg1) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public SPred buildRealPred(int realPredTag, SReal arg1, SReal arg2) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public SValue buildSelect(SMap map, SValue idx) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public SMap buildStore(SMap map, SValue idx, SValue val) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public SPred buildTrue() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public SValue buildValueConversion(Sort from, Sort to, SValue val) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public SPred buildXor(SPred arg1, SPred arg2) {
		// TODO Auto-generated method stub
		return null;
	}

	
	
	
}
