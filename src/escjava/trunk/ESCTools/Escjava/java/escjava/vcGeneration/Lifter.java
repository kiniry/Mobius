package escjava.vcGeneration;

import javafe.ast.*;
import javafe.tc.*;
import javafe.util.*;
import escjava.ast.*;
import escjava.translate.*;
import escjava.vcGeneration.NodeBuilder.PredSymbol;
import escjava.vcGeneration.NodeBuilder.Sort;
import escjava.ast.TagConstants;
import escjava.prover.Atom;

import java.io.*;
import java.util.Hashtable;
import java.util.Stack;
import java.util.regex.Pattern;

public class Lifter extends EscNodeBuilder
{
	private void trace(String msg)
	{
		ErrorSet.caution(msg);
	}
	
	class SortVar extends Sort
	{
		private Sort ref;
		
		public SortVar()
		{
			super("sortVar", null, null, null);
		}
		
		public Sort/*?*/ getSuperSort()
		{
			Assert.notFalse(ref != null);
			return ref.getSuperSort();
		}

		public Sort/*?*/ getMapFrom()
		{
			Assert.notFalse(ref != null);
			return ref.getMapFrom();
		}

		public Sort/*?*/ getMapTo()
		{
			Assert.notFalse(ref != null);
			return ref.getMapTo();
		}
		
		public boolean isFinalized()
		{
			if (ref == null) return false;
			if (ref instanceof SortVar)
				return ((SortVar)ref).isFinalized();
			return true;
		}
		
		boolean occurCheck(Sort s)
		{
			if (s == this)
				return true;
				
			if (s instanceof SortVar && !((SortVar)s).isFinalized())
			{
				return false;
			}
			else if (s.getMapFrom() != null) {
				return occurCheck(s.getMapFrom()) || occurCheck(s.getMapTo());
			} else return false;
		}
		
		public void assign(Sort s)
		{
			Assert.notFalse(ref == null);
			trace("assign: ?" + id + " <- " + s);
			if (occurCheck(s))
				ErrorSet.error("cyclic sort found");
			else
				ref = s;
		}
		
		public Sort follow()
		{
			if (ref != null && ref instanceof SortVar)
				return ((SortVar)ref).follow();
			return ref == null ? this : ref;
		}
		
		public String toString()
		{
			if (ref == null) return "?" + id;
			else return ref.toString();
		}
	}
	
	abstract class Term
	{	
		abstract public Sort getSort();
		abstract public void infer();
		
		public void printTo(StringBuffer sb)
		{
			sb.append(super.toString());		
		}
		
		public String toString()
		{
			StringBuffer sb = new StringBuffer();
			printTo(sb);
			return sb.toString();
		}
	}
	
	class QuantVariableRef extends Term
	{
		final public QuantVariable qvar;
		
		public QuantVariableRef(QuantVariable q) { qvar = q; }		
		public Sort getSort() { return qvar.type; }
		public void infer() { }
		
		public void printTo(StringBuffer sb)
		{
			sb.append("?" + qvar.name + ":" + qvar.type);
		}
	}
	
	class FnTerm extends Term
	{
		public FnSymbol fn;
		final public Term[] args;
		public int tag;
		final public Sort retType;
		
		public FnTerm(FnSymbol fn, Term[] args)
		{
			this.fn = fn;
			this.args = args;
			if (fn == symSelect || fn == symStore || fn == symAsField)
				retType = new SortVar();
			else
				retType = fn.retType;
		}
		
		public Sort getSort() { return retType; }
		
		void enforceArgType(int i, Sort r)
		{
			r = follow(r);
			Sort p = follow(args[i].getSort());
			
			if (isEarlySort (r, p))
				return;
			
			FnSymbol conv = null;
			
			int minpass = 2;
			if (p == sortValue)
				conv =
					r == sortInt ? symValueToInt : 
					r == sortRef ? symValueToRef : 
					r == sortBool ? symValueToBool : 
					r == sortPred ? symValueToPred :
					r == sortReal ? symValueToReal :
					null;
			else if (p == sortInt && r == sortReal) {
				conv = symIntToReal;
				minpass = 0;
			}
			
			if (pass >= 1 && r == sortPred && p == sortBool) {
				args[i] = new FnTerm(symIsTrue, new Term[] { args[i] });
			} else if (pass >= minpass && conv != null) {
				args[i] = new FnTerm(conv, new Term[] { args[i] });
			} else
				require(p, r, args[i] + ", which is arg #" + (1+i) + " of " + this);
		}
		
		public void infer()
		{
			trace("start infer " + pass + ": " + fn + " / " + this + " -> " + retType);
			
			if (args.length != fn.argumentTypes.length) {
				ErrorSet.error("wrong number of parameters to " + fn + " ---> " + this);
				return;
			}
			
			for (int i = 0; i < args.length; ++i)
				args[i].infer();			
			
			boolean skip = pass < lastPass;
			
			if (fn == symSelect)
			{
				Sort idx = new SortVar();
				Sort map = registerMapSort(idx, retType);
				
				enforceArgType(0, map);
				enforceArgType(1, idx);
			}
			else if (fn == symStore)
			{
				Sort idx = new SortVar();
				Sort val = new SortVar();
				Sort map = registerMapSort(idx, val);
				
				if (!isEarlySort(retType, map))
					unify(retType, map, this);				
				enforceArgType(0, map);
				enforceArgType(1, idx);
				enforceArgType(2, val);
			}
			else if (fn == symAnyEQ || fn == symAnyNE) {
				// we don't really want to enforce that, as we might
				// want to compare arrays to nulls for example
				/*
				Sort common = new SortVar();
				
				enforceArgType(0, common);
				enforceArgType(1, common);
				*/
				
				if (follow(args[0].getSort()) == sortPred ||
					follow(args[1].getSort()) == sortPred)
				{
					if (fn == symAnyEQ)
						fn = symIff;
					else
						fn = symXor;
					skip = false;
				}
			}
			else if (fn == symAsField) {
				Sort field = registerMapSort(new SortVar(), new SortVar(), sortField);
				
				enforceArgType(0, field);
				enforceArgType(1, sortType);				
				unify(field, retType, this);				
			}
			else if (fn == symFClosedTime) {
				Sort field = registerMapSort(new SortVar(), new SortVar(), sortField);
				
				enforceArgType(0, field);				
			} else skip = false;
			
			if (!skip)
				for (int i = 0; i < args.length; ++i)
					enforceArgType(i, fn.argumentTypes[i]);					
			
			trace("infer " + pass + ": " + fn + " / " + this + " -> " + retType);
		}
		
		public void printTo(StringBuffer sb)
		{
			sb.append(fn.name);
			
			if (args.length > 0) {
				sb.append("(");
				for (int i = 0; i < args.length; ++i) {
					args[i].printTo(sb);
					if (i != args.length - 1)
						sb.append(", ");
				}
				sb.append(")");
			}
			
			sb.append(":").append(retType);
		}
	}
	
	class QuantTerm extends Term
	{
		public final boolean universal;
		public final QuantVariable[] vars;
		public final Term[][] pats;
		public final Term[] nopats;
		public final Term body;
		
		public QuantTerm(boolean universal, QuantVariable[] vars, Term body, Term[][] pats, Term[] nopats)
		{
			this.universal = universal;
			this.vars = vars;
			this.body = body;
			this.pats = pats;
			this.nopats = nopats;		
		}
		
		public Sort getSort() { return sortPred; } 		
		public void infer()
		{			
			trace("infer start q " + pass + ": " + this);
			body.infer();
			unify(body.getSort(), sortPred, this);
			trace("infer q " + pass + ": " + this);
		}
		
		public void printTo(StringBuffer sb)
		{
			sb.append("forall [");
			for (int i = 0; i < vars.length; ++i)
				sb.append(vars[i].name + ":" + vars[i].type + /*"/" + vars[i].var.type +*/ ", ");
			sb.append("] ");
			body.printTo(sb);
		}
	}
	
	class QuantVariable
	{
		public final GenericVarDecl var;
		public final String name;
		public final Sort type;
		
		public QuantVariable(GenericVarDecl v, String n)
		{
			var = v;
			name = n;
			type = typeToSort(v.type);
		}
	}
	
	class IntLiteral extends Term
	{
		final public long value;
		public IntLiteral(long v) { value = v; }
		public Sort getSort() { return sortInt; }
		public void infer() { }
		public void printTo(StringBuffer sb) { sb.append(value); }
	}
	
	class RealLiteral extends Term
	{
		final public double value;
		public RealLiteral(double v) { value = v; }
		public Sort getSort() { return sortReal; } 
		public void infer() { }
	}
	
	class BoolLiteral extends Term
	{
		final public boolean value;
		public BoolLiteral(boolean v) {	value = v; }
		public Sort getSort() { return sortBool; }
		public void infer() { }
	}
	
	class StringLiteral extends Term
	{
		final public String value;
		public StringLiteral(String v) { value = v; }
		public Sort getSort() { return sortString; }
		public void infer() { }
		public void printTo(StringBuffer sb) { sb.append("\"" + value + "\""); }		
	}
	
	class NullLiteral extends Term
	{
		public NullLiteral() { }
		public Sort getSort() { return sortRef; }
		public void infer() { }
	}
	
	public PredSymbol symImplies = registerPredSymbol("%implies", new Sort[] { sortPred, sortPred }, TagConstants.BOOLIMPLIES);
	public PredSymbol symAnd = registerPredSymbol("%and.2", new Sort[] { sortPred, sortPred });
	public PredSymbol symIff = registerPredSymbol("%iff", new Sort[] { sortPred, sortPred }, TagConstants.BOOLEQ);
	public PredSymbol symXor = registerPredSymbol("%xor", new Sort[] { sortPred, sortPred }, TagConstants.BOOLNE);
	public PredSymbol symNot = registerPredSymbol("%not", new Sort[] { sortPred }, TagConstants.BOOLNOT);
	public PredSymbol symIntPred = registerPredSymbol("%int-pred", new Sort[] { sortInt, sortInt });
	public PredSymbol symRealPred = registerPredSymbol("%real-pred", new Sort[] { sortReal, sortReal });
	public FnSymbol symIntFn = registerFnSymbol("%int-pred", new Sort[] { sortInt, sortInt }, sortInt);
	public FnSymbol symRealFn = registerFnSymbol("%real-pred", new Sort[] { sortReal, sortReal }, sortReal);
	public FnSymbol symSelect = registerFnSymbol("%select", new Sort[] { sortMap, sortValue }, sortValue, TagConstants.SELECT);
	public FnSymbol symStore = registerFnSymbol("%store", new Sort[] { sortMap, sortValue, sortValue }, sortMap, TagConstants.STORE);
	public PredSymbol symAnyEQ = registerPredSymbol("%anyEQ", new Sort[] { sortValue, sortValue }, TagConstants.ANYEQ);
	public PredSymbol symAnyNE = registerPredSymbol("%anyNE", new Sort[] { sortValue, sortValue }, TagConstants.ANYNE);
	public PredSymbol symIsTrue = registerPredSymbol("%isTrue", new Sort[] { sortBool });
	
    public FnSymbol symValueToRef = registerFnSymbol("%valueToRef", new Sort[] { sortValue }, sortRef);
    public FnSymbol symValueToInt = registerFnSymbol("%valueToInt", new Sort[] { sortValue }, sortInt);
    public FnSymbol symValueToBool = registerFnSymbol("%valueToBool", new Sort[] { sortValue }, sortBool);
    public FnSymbol symValueToReal = registerFnSymbol("%valueToReal", new Sort[] { sortValue }, sortReal);
    public FnSymbol symIntToReal = registerFnSymbol("%intToReal", new Sort[] { sortInt }, sortReal);
    public PredSymbol symValueToPred = registerPredSymbol("%valueToPred", new Sort[] { sortValue });
    
    // should probably be in EscNodeBuilder:    
    public FnSymbol symIntern = registerFnSymbol("|:intern|", new Sort[] { sortInt, sortInt }, sortString, TagConstants.INTERN);
    public PredSymbol symInterned = registerPredSymbol("|:interned|", new Sort[] { sortString }, TagConstants.INTERNED);
    public FnSymbol symStringCat = registerFnSymbol("stringCat", new Sort[] { sortString, sortString, sortTime }, sortString, TagConstants.STRINGCAT);
    // the 3rd argument seems to be sometimes int and sometimes string
    public PredSymbol symStringCatP = registerPredSymbol("stringCatP", new Sort[] { sortString, sortString, sortValue, sortTime, sortTime }, TagConstants.STRINGCATP);
    // these two should go to NodeBuilder
    public FnSymbol symIntegralNeg = registerFnSymbol("integralNeg", new Sort[] { sortInt }, sortInt, TagConstants.INTEGRALNEG);
    public FnSymbol symFloatingNeg = registerFnSymbol("floatingNeg", new Sort[] { sortReal }, sortReal, TagConstants.FLOATINGNEG);
    // this is just ITE
    public FnSymbol symTermConditional = registerFnSymbol("termConditional", new Sort[] { sortPred, sortValue, sortValue }, sortValue, TagConstants.CONDITIONAL);
    public PredSymbol symNonNullElems = registerPredSymbol("nonnullelements", new Sort[] { sortArray, sortElems }, TagConstants.ELEMSNONNULL);
    public FnSymbol symElemType = registerFnSymbol("elemtype", new Sort[] { sortType }, sortType, TagConstants.ELEMTYPE);
    public FnSymbol symMax = registerFnSymbol("max", new Sort[] { sortLockSet }, sortLock, TagConstants.MAX);
    public FnSymbol symArrayMake = registerFnSymbol("arrayMake", new Sort[] { sortTime, sortTime, sortShape, sortType, sortValue }, sortArray, TagConstants.ARRAYMAKE);
    public FnSymbol symClassLiteral = registerFnSymbol("classLiteral", new Sort[] { sortType }, sortRef, TagConstants.CLASSLITERALFUNC);
    
    public FnSymbol symIntShiftUR = registerFnSymbol("intShiftUR", new Sort[] { sortInt, sortInt }, sortInt, TagConstants.INTSHIFTRU);
    public FnSymbol symIntShiftL = registerFnSymbol("intShiftL", new Sort[] { sortInt, sortInt }, sortInt, TagConstants.INTSHIFTL);
    public FnSymbol symIntShiftAR = registerFnSymbol("intShiftAR", new Sort[] { sortInt, sortInt }, sortInt, TagConstants.INTSHIFTR);
    public FnSymbol symLongShiftAR = registerFnSymbol("longShiftAR", new Sort[] { sortInt, sortInt }, sortInt, TagConstants.LONGSHIFTR);
    public FnSymbol symLongShiftUR = registerFnSymbol("longShiftUR", new Sort[] { sortInt, sortInt }, sortInt, TagConstants.LONGSHIFTRU);
    public FnSymbol symLongShiftL = registerFnSymbol("longShiftL", new Sort[] { sortInt, sortInt }, sortInt, TagConstants.LONGSHIFTL);
    // end
	
	// we just want Sort and the like, don't implement anything	
	static class Die extends RuntimeException { }
	public SAny buildFnCall(FnSymbol fn, SAny[] args) { throw new Die(); }
	public SAny buildConstantRef(FnSymbol c) { throw new Die(); }
	public SAny buildQVarRef(QuantVar v) { throw new Die(); }
	public SPred buildPredCall(PredSymbol fn, SAny[] args) { throw new Die(); }
	
	public SPred buildImplies(SPred arg1, SPred arg2) { throw new Die(); }
	public SPred buildIff(SPred arg1, SPred arg2) { throw new Die(); }
	public SPred buildXor(SPred arg1, SPred arg2) { throw new Die(); }
	public SPred buildAnd(SPred[] args) { throw new Die(); }
	public SPred buildOr(SPred[] args) { throw new Die(); }
	public SPred buildNot(SPred arg) { throw new Die(); }
	public SPred buildForAll(QuantVar[] vars, SPred body, STerm[][] pats, STerm[] nopats) { throw new Die(); }
	public SPred buildExists(QuantVar[] vars, SPred body) { throw new Die(); }
	public SPred buildIntPred(int intPredTag, SInt arg1, SInt arg2) { throw new Die(); }
	public SInt buildIntFun(int intFunTag, SInt arg1, SInt arg2) { throw new Die(); }
	public SPred buildRealPred(int realPredTag, SReal arg1, SReal arg2) { throw new Die(); }
	public SReal buildRealFun(int realFunTag, SReal arg1, SReal arg2) { throw new Die(); }
	public SString buildString(String s) { throw new Die(); }
	public SBool buildBool(boolean b) { throw new Die(); }
	public SInt buildInt(long n) { throw new Die(); }
	public SReal buildReal(double f) { throw new Die(); }
	public SRef buildNull() { throw new Die(); }
	public SValue buildSelect(SMap map, SValue idx) { throw new Die(); }
	public SMap buildStore(SMap map, SValue idx, SValue val) { throw new Die(); }
	public SPred buildAnyEQ(SAny arg1, SAny arg2) { throw new Die(); }
	public SPred buildAnyNE(SAny arg1, SAny arg2) { throw new Die(); }
	
	int pass;
	final int lastPass = 3;
	
	boolean isEarlySort(Sort s, Sort p)
	{
		return isEarlySort(s) || isEarlySort(p);
	}
	
	boolean isEarlySort(Sort s)
	{
		s = follow(s);
		
		if (pass == 0)
			return s == sortAny || s == sortPred || s == sortValue || s == sortRef;
		else if (pass == 1)
			return s == sortAny || s == sortPred || s == sortValue;
		else if (pass == 2)
			return s == sortAny || s == sortPred;
		else
			return false;
	}
	
	public void run()
	{
		Term m = transform(main);
		
		pass = 0;
		while (pass <= lastPass) {
			m.infer();
			pass++;
		}
	}
	
	public Lifter(Expr e)
	{
		main = e;
	}
	
	final Stack quantifiedVars = new Stack();
	final Hashtable symbolTypes = new Hashtable();
	final Term[] emptyTerms = new Term[0];
	final Expr main;
	
	Sort follow(Sort s)
	{
		if (s != null && s instanceof SortVar)
			return ((SortVar)s).follow();
		return s;		
	}
	
	private boolean isFinalized(Sort s)
	{
		return s != null && !(s instanceof SortVar && !((SortVar)s).isFinalized());
	}
	
	// make sure s1<:s2
	private void require(Sort s1, Sort s2, Object where)
	{
		s1 = follow(s1);
		s2 = follow(s2);
		
		if (s1 == s2) return;
		
		if (!isFinalized(s1))
			((SortVar)s1).assign(s2);
		else if (!isFinalized(s2))
			((SortVar)s2).assign(s1);
		else if (s1.isSubSortOf(s2))
		{}
		else if (s1.getMapFrom() != null && s2.getMapFrom() != null) {
			if (isFinalized(s2.getMapTo()) && s2.getMapTo().getMapFrom() != null) {
				unify(sortRef, s1.getMapFrom(), where);
				unify(sortRef, s2.getMapFrom(), where);
				unify(sortArrayValue, s1.getMapTo(), where);
				unify(sortArrayValue, s2.getMapTo(), where);
			}
			else {
				unify(s1.getMapFrom(), s2.getMapFrom(), where);
				unify(s1.getMapTo(), s2.getMapTo(), where);
			}
		}
		else
			ErrorSet.error("the sort >" + s1 + "< is required to be subsort of >" + s2 + "< in " + where);			
	}
	
	private void unify(Sort s1, Sort s2, Object where)
	{
		require(s1, s2, where);
		require(s2, s1, where);
	}
	
	private Term symbolRef(String name, Sort s)
	{
		FnSymbol fn = getFnSymbol(name, 0);
		if (s != null)
			require(s, fn.retType, "symbol ref " + name);
		return new FnTerm(fn, emptyTerms);
	}
	
	private Term symbolRef(String name)
	{
		return symbolRef(name, null);
	}
	
	private FnSymbol getFnSymbol(String name, int arity)
	{
		name = name + "." + arity;
		if (!symbolTypes.containsKey(name)) {			
			FnSymbol fn;
			if (arity == 0)
				fn = registerConstant(name, new SortVar());
			else {
				Sort[] args = new Sort[arity];
				for (int i = 0; i < arity; ++i)
					args[i] = new SortVar();
				fn = registerFnSymbol(name, args, new SortVar());
			}
			symbolTypes.put(name, fn);
			if (arity == 0 && name.startsWith("elems<") || name.equals("elems"))
				unify(fn.retType, sortElems, "elems<* hack");
			if (arity == 0 && name.startsWith("owner:") || name.equals("owner"))
				unify(fn.retType, sortOwner, "owner hack");
			return fn;
		}
		return (FnSymbol)symbolTypes.get(name);
	}
	
	private Term transform(/*@ non_null @*/ASTNode n)
	{
		//ErrorSet.caution("enter " + TagConstants.toString(n.getTag()) + " " + n);
		Term t = doTransform(n);
		//ErrorSet.caution("exit " + TagConstants.toString(n.getTag()));
		return t;
	}
	
	private Sort typeToSort(Type t)
	{
		switch (t.getTag()) {
		case TagConstants.ARRAYTYPE:
			return sortArray;
		case TagConstants.LONGTYPE:
		case TagConstants.INTTYPE:
			return sortInt;
		case TagConstants.TYPENAME:
			return sortRef;
		case TagConstants.ANY:
			return new SortVar();
		default:
			ErrorSet.caution("unknown type: " + TagConstants.toString(t.getTag()));
			return new SortVar();
		}
	}
	
	private Pattern number = Pattern.compile("[0-9]+");
	
	private Term doTransform(/*@ non_null @*/ASTNode n)
	{		
		// declarations & instancations
		int nbChilds = n.childCount();
		Object o = null;
		
		// all types checked are in alphabetical order
		if (n instanceof ArrayType) {			
			ArrayType m = (ArrayType) n;			
			return new FnTerm(symArray, new Term[] { transform(m.elemType) });
			
		} else if (n instanceof LiteralExpr) {
			LiteralExpr m = (LiteralExpr) n;
			
			switch (m.getTag()) {
			case TagConstants.STRINGLIT: 
				return new StringLiteral((String) m.value);
			case TagConstants.BOOLEANLIT: 
				return new BoolLiteral(((Boolean) m.value).booleanValue());
			case TagConstants.INTLIT:
			case TagConstants.CHARLIT:
				return new IntLiteral(((Integer) m.value).intValue());
			case TagConstants.LONGLIT:
				return new IntLiteral(((Long) m.value).longValue());
			case TagConstants.FLOATLIT:
				return new RealLiteral(((Float) m.value).floatValue());
			case TagConstants.DOUBLELIT:
				return new RealLiteral(((Double) m.value).doubleValue());
			case TagConstants.NULLLIT:
				return new NullLiteral();
			case TagConstants.SYMBOLLIT: {
				String v = (String)m.value;
				if (number.matcher(v).matches())
					return new IntLiteral(Long.parseLong(v));
				else
					return symbolRef(v);
			}
			default:
				ErrorSet.fatal("Instanceof LiteralExpr, case missed :"
						+ TagConstants.toString(m.getTag()));
				return null;
			}
		}
		else if (n instanceof LabelExpr) {
			return transform(((LabelExpr)n).expr);
		}
		// name of a method
		else if (n instanceof NaryExpr) {
			NaryExpr m = (NaryExpr) n;
			
			FnSymbol fn = null;
			int tag = 0;
			int arity = m.childCount() - 1;
			
			switch (m.getTag()) {
			// hack: REFEQ is used to compare integers
			case TagConstants.REFEQ:
				fn = symAnyEQ; break;
			case TagConstants.REFNE:
				fn = symAnyNE; break;
				
			case TagConstants.BOOLAND:
			case TagConstants.BOOLANDX:
			case TagConstants.BOOLOR:
				fn = getFnSymbol(m.getTag() == TagConstants.BOOLOR ? "%or" : "%and",
								 arity);
				for (int i = 0; i < fn.argumentTypes.length; ++i)
					unify(fn.argumentTypes[i], sortPred, "and/or");
				unify(fn.retType, sortPred, "and/or");
				break;
			
			// integral comparisons
			case TagConstants.INTEGRALEQ:
				fn = symIntPred; tag = predEQ; break;
			case TagConstants.INTEGRALGE:
				fn = symIntPred; tag = predGE; break;
			case TagConstants.INTEGRALGT:
				fn = symIntPred; tag = predGT; break;
			case TagConstants.INTEGRALLE:
				fn = symIntPred; tag = predLE; break;
			case TagConstants.INTEGRALLT:
				fn = symIntPred; tag = predLT; break;
			case TagConstants.INTEGRALNE:
				fn = symIntPred; tag = predNE; break;
			
			// int functions
			case TagConstants.INTEGRALADD:
				fn = symIntFn; tag = funADD; break;
			case TagConstants.INTEGRALDIV:
				fn = symIntFn; tag = funDIV; break;
			case TagConstants.INTEGRALMOD:
				fn = symIntFn; tag = funMOD; break;
			case TagConstants.INTEGRALMUL:
				fn = symIntFn; tag = funMUL; break;
			case TagConstants.INTEGRALSUB:
				fn = symIntFn; tag = funSUB; break;
				
			// real comparisons
			case TagConstants.FLOATINGEQ:
				fn = symRealPred; tag = predEQ; break;
			case TagConstants.FLOATINGGE:
				fn = symRealPred; tag = predGE; break;
			case TagConstants.FLOATINGGT:
				fn = symRealPred; tag = predGT; break;
			case TagConstants.FLOATINGLE:
				fn = symRealPred; tag = predLE; break;
			case TagConstants.FLOATINGLT:
				fn = symRealPred; tag = predLT; break;
			case TagConstants.FLOATINGNE:
				fn = symRealPred; tag = predNE; break;
			
			// real functions
			case TagConstants.FLOATINGADD:
				fn = symRealFn; tag = funADD; break;
			case TagConstants.FLOATINGDIV:
				fn = symRealFn; tag = funDIV; break;
			case TagConstants.FLOATINGMOD:
				fn = symRealFn; tag = funMOD; break;
			case TagConstants.FLOATINGMUL:
				fn = symRealFn; tag = funMUL; break;
			case TagConstants.FLOATINGSUB:
				fn = symRealFn; tag = funSUB; break;
			
			case TagConstants.DTTFSA: {
				LiteralExpr lit = (LiteralExpr)n.childAt(2);
				String op = (String)lit.value;
				if (arity == 1) {
					return symbolRef(op);
				} else if (op.equals("identity")) {
					Assert.notFalse(arity == 2);
					return transform((ASTNode)n.childAt(3));
				} else {
					arity--;
					fn = getFnSymbol(op, arity);
					Term[] args = new Term[arity];
					for (int i = 0; i < arity; ++i)
						args[i] = transform((ASTNode)n.childAt(i+2));
					return new FnTerm(fn, args); 
				}
			}
			
			case TagConstants.SUM:
				Assert.fail("sum unhandled"); break;
				
			case TagConstants.METHODCALL:
				fn = getFnSymbol(m.methodName.toString(), arity); break;
				
			default:
				Integer itag = new Integer(m.getTag());
				if (fnSymbolsByTag.containsKey(itag))
				{
					Object v = fnSymbolsByTag.get(itag); 
					if (v instanceof FnSymbol)
						fn = (FnSymbol)v;
					else if (v instanceof PredSymbol)
						fn = (PredSymbol)v;
					else
						Assert.fail("pff");					
				} else {
					ErrorSet.fatal("translating old gc tree, methodName not recognized "
						+ TagConstants.toString(m.getTag()) );
				}
			}
			
			Term[] args = new Term[arity];
			for (int i = 0; i < arity; ++i)
				args[i] = transform((ASTNode)n.childAt(i+1));
			return new FnTerm(fn, args); 
			
		} else if (n instanceof PrimitiveType) { // javafe/Type
			// this means this variable represent a primitive java type like
			// string, boolean or Java.lang.Object
			
			PrimitiveType m = (PrimitiveType) n;
			String s = javafe.ast.TagConstants.toString(m.getTag());
			return symbolRef(s, sortType);
			
		} else if (n instanceof QuantifiedExpr) {
			QuantifiedExpr m = (QuantifiedExpr) n;
			
			String s = TagConstants.toString(m.getTag());
			
			boolean universal = false;
			
			if (m.getTag() == TagConstants.FORALL)
				universal = true;
			else if (m.getTag() == TagConstants.EXISTS)
				universal = false;
			else
				Assert.fail("QuantifiedExpr, unhandled tag");
			
			QuantVariable[] vars = new QuantVariable[m.vars.size()];
			for (int i = 0; i < m.vars.size(); ++i) {
				GenericVarDecl v = m.vars.elementAt(i);
				vars[i] = new QuantVariable(v, UniqName.variable(v));
				quantifiedVars.push(vars[i]);
			}
			
			Term[][] pats;
			Term[] nopats;
			
			if (m.pats != null) {
				pats = new Term[m.pats.size()][];
				for (int i = 0; i < pats.length; ++i)
					// FIXME what about multitriggers?
					pats[i] = new Term[] { transform(m.pats.elementAt(i)) };
			} else { 
				pats = new Term[0][];
			}
			
			if (m.nopats != null) {
				nopats = new Term[m.nopats.size()];
				for (int i = 0; i < nopats.length; ++i)
					nopats[i] = transform(m.nopats.elementAt(i));
			}else {
				nopats = new Term[0];
			}
			
			Term body = transform(m.expr);
			
			if (m.rangeExpr != null) {
				Term range = transform(m.rangeExpr);
				if (range instanceof BoolLiteral && ((BoolLiteral)range).value == true)
				{}
				else {
					body = new FnTerm(universal ? symImplies : symAnd, new Term[] { range, body });
				}
			}
			
			for (int i = 0; i < m.vars.size(); ++i)
				quantifiedVars.pop();
			
			return new QuantTerm(universal, vars, body, pats, nopats);
			
		} else if (n instanceof SimpleName) {
			SimpleName m = (SimpleName) n;			
			
			// it seems that this node is under a TypeName node all the time
			// and that all the information is in the TypeName node.
			// that's why we don't create a new node here.
			
			ErrorSet.fatal("SimpleName: "+m);
			return null;
			
		} else if (n instanceof SubstExpr) {
			SubstExpr m = (SubstExpr) n;
			
			ErrorSet.fatal("SubstExpr viewed and not handled");
			return null;
			
		} else if (n instanceof TypeDecl) {						
			TypeDecl m = (TypeDecl) n;
			// this represents a type
			
			String s = new String(m.id.chars);
			
			ErrorSet.fatal("ignored TypeDecl " + s);
			return null;
			
		} else if (n instanceof TypeExpr) {
			TypeExpr m = (TypeExpr) n;
			return transform(m.type);
			
		} else if (n instanceof TypeName) { // javafe/Type
			// this represents a type			
			TypeName m = (TypeName) n;
			String s = m.name.printName();
			
			Assert.notFalse(s != null, 
					"case n instanceof TypeName, warning null reference not expected");
			
			return symbolRef(s, sortType);
			
		} else if (n instanceof TypeSig) {
			TypeSig m = (TypeSig) n;
			return symbolRef(m.getExternalName(), sortType);
			
		} else if (n instanceof VariableAccess) {
			VariableAccess m = (VariableAccess) n;
			
			for (int i = 0; i < quantifiedVars.size(); ++i) {
				QuantVariable q = (QuantVariable)quantifiedVars.elementAt(i);
				if (q.var == m.decl)
					return new QuantVariableRef(q);
			}
			
			return symbolRef (UniqName.variable(m.decl));
			
		} else {
			ErrorSet.fatal("unhandled tag " + TagConstants.toString(n.getTag()));
			return null;
		}
	}	
}
