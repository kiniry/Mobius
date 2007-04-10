package mobius.sortedProver;

import java.io.PrintStream;
import java.util.ArrayList;
import java.util.Enumeration;
import java.util.Hashtable;
import java.util.Stack;
import java.util.regex.Pattern;

import mobius.sortedProver.lifter.members.BoolLiteral;
import mobius.sortedProver.lifter.members.FnTerm;
import mobius.sortedProver.lifter.members.IntLiteral;
import mobius.sortedProver.lifter.members.LabeledTerm;
import mobius.sortedProver.lifter.members.NullLiteral;
import mobius.sortedProver.lifter.members.QuantTerm;
import mobius.sortedProver.lifter.members.QuantVariable;
import mobius.sortedProver.lifter.members.QuantVariableRef;
import mobius.sortedProver.lifter.members.RealLiteral;
import mobius.sortedProver.lifter.members.SortVar;
import mobius.sortedProver.lifter.members.Term;
import mobius.sortedProver.nodebuilder.members.FnSymbol;
import mobius.sortedProver.nodebuilder.members.PredSymbol;
import mobius.sortedProver.nodebuilder.members.QuantVar;
import mobius.sortedProver.nodebuilder.members.Sort;

import javafe.ast.ASTNode;
import javafe.ast.ArrayType;
import javafe.ast.ClassDecl;
import javafe.ast.ConstructorDecl;
import javafe.ast.Expr;
import javafe.ast.ExprVec;
import javafe.ast.FieldDecl;
import javafe.ast.FormalParaDecl;
import javafe.ast.GenericVarDecl;
import javafe.ast.LiteralExpr;
import javafe.ast.LocalVarDecl;
import javafe.ast.MethodDecl;
import javafe.ast.PrettyPrint;
import javafe.ast.PrimitiveType;
import javafe.ast.SimpleName;
import javafe.ast.Type;
import javafe.ast.TypeDecl;
import javafe.ast.VariableAccess;
import javafe.tc.TypeCheck;
import javafe.tc.TypeSig;
import javafe.tc.Types;
import javafe.util.Assert;
import javafe.util.ErrorSet;
import javafe.util.Info;
import javafe.util.Location;
import escjava.ast.LabelExpr;
import escjava.ast.Modifiers;
import escjava.ast.NaryExpr;
import escjava.ast.QuantifiedExpr;
import escjava.ast.SubstExpr;
import escjava.ast.TagConstants;
import escjava.ast.TypeExpr;
import escjava.backpred.BackPred;
import escjava.backpred.FindContributors;
import escjava.translate.GC;
import escjava.translate.TrAnExpr;
import escjava.translate.UniqName;

/*@ non_null_by_default @*/
public class Lifter extends EscNodeBuilder
{
	public final static boolean doTrace = false;
	final Stack quantifiedVars = new Stack();
	final Hashtable symbolTypes = new Hashtable();
	final Term[] emptyTerms = new Term[0];
	final EscNodeBuilder builder;
	final SortedBackPred backPred = new SortedBackPred();	

	int methodNo = 0;
	public static final int lastPass = 3;
	
	// public interface
	public SPred convert(Expr main) 
	{
		methodNo++;
		return doConvert(transform(main));
	}
	
	public Lifter(EscNodeBuilder b)
	{
		builder = b;
	} 
	
	public SPred generateBackPred(FindContributors scope)
	{
		Assert.notFalse(methodNo == 0);
		
		backPred.genTypeBackPred(scope, System.err);

		Term[] terms = new Term[backPred.axioms.size()];
		terms = (Term[])backPred.axioms.toArray(terms);
		Term axioms = new FnTerm(giantBoolConective(TagConstants.BOOLAND, terms.length), terms);
		
		SAny[] dist = new SAny[backPred.distinct.size()];
		dumpBuilder = builder;
		for (int i = 0; i < dist.length; ++i)
			dist[i] = ((Term)backPred.distinct.get(i)).dumpAny();
		dumpBuilder = null;
		
		SPred and1 = doConvert(axioms);
		SPred and2 = builder.buildDistinct(dist);
		methodNo++;
		return builder.buildAnd(new SPred[] { and1, and2 });
	}
	// end public interface
	
	public static PredSymbol symImplies = registerPredSymbol("%implies", new Sort[] { sortPred, sortPred }, TagConstants.BOOLIMPLIES);
	public static PredSymbol symOr = registerPredSymbol("%or", new Sort[] { sortPred, sortPred });
	public static PredSymbol symAnd = registerPredSymbol("%and", new Sort[] { sortPred, sortPred });
	public static PredSymbol symIff = registerPredSymbol("%iff", new Sort[] { sortPred, sortPred }, TagConstants.BOOLEQ);
	public static PredSymbol symXor = registerPredSymbol("%xor", new Sort[] { sortPred, sortPred }, TagConstants.BOOLNE);
	public static PredSymbol symNot = registerPredSymbol("%not", new Sort[] { sortPred }, TagConstants.BOOLNOT);
    public static FnSymbol symTermConditional = registerFnSymbol("%ite", new Sort[] { sortPred, sortValue, sortValue }, sortValue, TagConstants.CONDITIONAL);
	public static  PredSymbol symIntPred = registerPredSymbol("%int-pred", new Sort[] { sortInt, sortInt });
	public static  PredSymbol symRealPred = registerPredSymbol("%real-pred", new Sort[] { sortReal, sortReal });
	public static  FnSymbol symIntFn = registerFnSymbol("%int-pred", new Sort[] { sortInt, sortInt }, sortInt);
	public static  FnSymbol symRealFn = registerFnSymbol("%real-pred", new Sort[] { sortReal, sortReal }, sortReal);
    public static  FnSymbol symIntegralNeg = registerFnSymbol("%integralNeg", new Sort[] { sortInt }, sortInt, TagConstants.INTEGRALNEG);
    public static  FnSymbol symFloatingNeg = registerFnSymbol("%floatingNeg", new Sort[] { sortReal }, sortReal, TagConstants.FLOATINGNEG);    
	public static  FnSymbol symSelect = registerFnSymbol("%select", new Sort[] { sortMap, sortValue }, sortValue, TagConstants.SELECT);
	public static  FnSymbol symStore = registerFnSymbol("%store", new Sort[] { sortMap, sortValue, sortValue }, sortMap, TagConstants.STORE);
	public static  PredSymbol symAnyEQ = registerPredSymbol("%anyEQ", new Sort[] { sortValue, sortValue }, TagConstants.ANYEQ);
	public static  PredSymbol symAnyNE = registerPredSymbol("%anyNE", new Sort[] { sortValue, sortValue }, TagConstants.ANYNE);
	public static  PredSymbol symIsTrue = registerPredSymbol("%isTrue", new Sort[] { sortBool });
	
    public static  FnSymbol symValueToRef = registerFnSymbol("%valueToRef", new Sort[] { sortValue }, sortRef);
    public static  FnSymbol symValueToInt = registerFnSymbol("%valueToInt", new Sort[] { sortValue }, sortInt);
    public static  FnSymbol symValueToBool = registerFnSymbol("%valueToBool", new Sort[] { sortValue }, sortBool);
    public static  FnSymbol symValueToReal = registerFnSymbol("%valueToReal", new Sort[] { sortValue }, sortReal);
    public static  FnSymbol symIntToReal = registerFnSymbol("%intToReal", new Sort[] { sortInt }, sortReal);
    
    public static  PredSymbol symValueToPred = registerPredSymbol("%valueToPred", new Sort[] { sortValue });
    public static  FnSymbol symPredToBool = registerFnSymbol("%predToBool", new Sort[] { sortPred }, sortBool);    
    
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
	public SValue buildITE(SPred cond, SValue then_part, SValue else_part) { throw new Die(); }
	public SPred buildTrue() { throw new Die(); }
	public SPred buildDistinct(SAny[] terms) { throw new Die(); }
	public SPred buildLabel(boolean positive, String name, SPred pred) { throw new Die(); }
	public SPred buildForAll(QuantVar[] vars, SPred body, STerm[][] pats, STerm[] nopats) { throw new Die(); }
	public SPred buildExists(QuantVar[] vars, SPred body) { throw new Die(); }
	public SPred buildIntPred(int intPredTag, SInt arg1, SInt arg2) { throw new Die(); }
	public SInt buildIntFun(int intFunTag, SInt arg1, SInt arg2) { throw new Die(); }
	public SPred buildRealPred(int realPredTag, SReal arg1, SReal arg2) { throw new Die(); }
	public SReal buildRealFun(int realFunTag, SReal arg1, SReal arg2) { throw new Die(); }
	public SInt buildIntFun(int intFunTag, SInt arg1) { throw new Die(); }
	public SReal buildRealFun(int realFunTag, SReal arg1) { throw new Die(); }
	public SBool buildBool(boolean b) { throw new Die(); }
	public SInt buildInt(long n) { throw new Die(); }
	public SReal buildReal(double f) { throw new Die(); }
	public SRef buildNull() { throw new Die(); }
	public SValue buildSelect(SMap map, SValue idx) { throw new Die(); }
	public SMap buildStore(SMap map, SValue idx, SValue val) { throw new Die(); }
	public SPred buildAnyEQ(SAny arg1, SAny arg2) { throw new Die(); }
	public SPred buildAnyNE(SAny arg1, SAny arg2) { throw new Die(); }
	public SValue buildValueConversion(Sort from, Sort to, SValue val) { throw new Die(); }
	public SPred buildIsTrue(SBool val) { throw new Die(); }


	
	SPred doConvert(Term root) 
	{	int pass;	
		pass = 0;
		while (pass <= lastPass) {
			root.infer(pass);
			pass++;
		}
		
		return build(root);
	}
	
	SPred build(Term root)
	{
		dumpBuilder = builder;
		stringConstants.clear();
		distinctSymbols.clear();
		
		root.enforceLabelSense(-1);
		SPred res = root.dumpPred();
		
		SPred[] assumptions = new SPred[stringConstants.size() * 2 + 1];
		
		for (int i = 0; i < stringConstants.size(); ++i) {
			SRef str = ((Term)stringConstants.get(i)).dumpRef();
			assumptions[2*i] = dumpBuilder.buildAnyNE(str, dumpBuilder.buildNull());
			assumptions[2*i+1] = dumpBuilder.buildAnyEQ(
					dumpBuilder.buildFnCall(symTypeOf, new SAny[] { str }),
					symbolRef("T_java.lang.String", sortType).dumpAny());
		}
		
		SAny[] terms = new SAny[distinctSymbols.size()];
		for (int i = 0; i < terms.length; ++i)
			terms[i] = ((Term)distinctSymbols.get(i)).dumpAny();
		assumptions[stringConstants.size()*2] = 
			terms.length == 0 ? dumpBuilder.buildTrue() : dumpBuilder.buildDistinct(terms);
		
		res = dumpBuilder.buildImplies(dumpBuilder.buildAnd(assumptions), res);
		
					
		dumpBuilder = null;
		return res;
	}
	
	public static Sort follow(Sort s)
	{
		return s.theRealThing();
	}
	
	public static boolean isFinalized(/*@ nullable @*/Sort s)
	{
		return s != null && !(s instanceof SortVar && !((SortVar)s).isFinalized());
	}
	
	// make sure s1<:s2
	public static boolean require(Sort s1, Sort s2, Object where)
	{
		s1 = follow(s1);
		s2 = follow(s2);
		
		if (s1 == s2) return true;
		
		if (!isFinalized(s1))
			((SortVar)s1).assign(s2);
		else if (!isFinalized(s2))
			((SortVar)s2).assign(s1);
		else if (s1.isSubSortOf(s2))
		{}
		else if (s1.getMapFrom() != null && s2.getMapFrom() != null) {
			if (isFinalized(s2.getMapTo()) && s2.getMapTo().getMapFrom() != null) {
				return unify(sortRef, s1.getMapFrom(), where) &&
					   unify(sortRef, s2.getMapFrom(), where) &&
					   unify(sortArrayValue, s1.getMapTo(), where) &&
					   unify(sortArrayValue, s2.getMapTo(), where);
			}
			else {
				return unify(s1.getMapFrom(), s2.getMapFrom(), where) &&
					   unify(s1.getMapTo(), s2.getMapTo(), where);
			}
		}
		else {
			ErrorSet.error("the sort >" + s1 + "< is required to be subsort of >" + s2 + "< in " + where);
			return false;
		}
		
		return true;
	}
	
	public static boolean unify(Sort s1, Sort s2, Object where)
	{
		return require(s1, s2, where) && require(s2, s1, where);
	}
	
	FnTerm symbolRef(String name, /*@ nullable @*/Sort s)
	{
		FnSymbol fn = getFnSymbol(name, 0);
		if (s != null)
			if (!require(s, fn.retType, "symbol ref"))
				ErrorSet.error("symbol ref " + name);
		return new FnTerm(fn, emptyTerms);
	}
	
	FnTerm symbolRef(String name)
	{
		return symbolRef(name, null);
	}
	
	FnSymbol getFnSymbol(String name, int arity)
	{
		String nameCur = name + "." + arity + "." + methodNo;
		String name0 = name + "." + arity + ".0";
		
		if (symbolTypes.containsKey(nameCur))
			return (FnSymbol)symbolTypes.get(nameCur);
		
		if (symbolTypes.containsKey(name0))
			return (FnSymbol)symbolTypes.get(name0);
		
		FnSymbol fn;
		if (arity == 0)
			fn = registerConstant(name, new SortVar());
		else {
			Sort[] args = new Sort[arity];
			for (int i = 0; i < arity; ++i)
				args[i] = new SortVar();
			fn = registerFnSymbol(name, args, new SortVar());
		}
		symbolTypes.put(nameCur, fn);
		if (arity == 0 && name.startsWith("elems") && 
				(name.startsWith("elems<") || 
						name.equals("elems") ||
						name.startsWith("elems@") ||
						name.startsWith("elems-") ||
						name.startsWith("elems:")))
			unify(fn.retType, sortElems, "elems* hack");
		if (arity == 0 && name.startsWith("owner:") || name.equals("owner"))
			unify(fn.retType, sortOwner, "owner hack");
		return fn;
	}
	
	public static void trace(String msg)
	{
		Assert.notFalse (doTrace);
		ErrorSet.caution(msg);
	}
		
	public static Sort typeToSort(Type t)
	{
		switch (t.getTag()) {
		case TagConstants.ARRAYTYPE:
			return sortArray;
			
		case TagConstants.BOOLEANTYPE:
			return sortBool;
		
		case TagConstants.DOUBLETYPE:
		case TagConstants.FLOATTYPE:
			return sortReal;
			
		case TagConstants.BYTETYPE:
		case TagConstants.SHORTTYPE:
		case TagConstants.INTTYPE:
		case TagConstants.CHARTYPE:
		case TagConstants.LONGTYPE:
		case TagConstants.BIGINTTYPE:
			return sortInt;
			
		case TagConstants.TYPESIG:
		case TagConstants.TYPENAME:
			return sortRef;
			
		case TagConstants.ANY:
			return new SortVar();
			
		default:
			ErrorSet.caution("unknown type: " + TagConstants.toString(t.getTag()) + ":" + PrettyPrint.inst.toString(t));
			
			return new SortVar();
		}
	}
	
	FnSymbol giantBoolConective(int tag, int arity) {
		FnSymbol fn;
		fn = getFnSymbol(tag == TagConstants.BOOLOR ? "%or" : "%and",
						 arity);
		for (int i = 0; i < fn.argumentTypes.length; ++i)
			unify(fn.argumentTypes[i], sortPred, "and/or");
		unify(fn.retType, sortPred, "and/or");
		return fn;
	}	
	private Pattern number = Pattern.compile("[0-9]+");	
	Term doTransform(ASTNode n)
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
				String s = "S_" + UniqName.locToSuffix(m.loc);
				FnTerm f = symbolRef(s, sortString);
				f.isStringConst = true;
				return f;
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
				else {
					//ErrorSet.caution("symbol lit " + v);
					FnTerm a = symbolRef(v);
					a.isDistinctSymbol = true;
					return a;
				}
			}
			default:
				ErrorSet.fatal("Instanceof LiteralExpr, case missed :"
						+ TagConstants.toString(m.getTag()));
				return null;
			}
		}
		else if (n instanceof LabelExpr) {
			LabelExpr l = ((LabelExpr)n);			
			return new LabeledTerm(l.positive, l.label.toString(), transform(l.expr));
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
				fn = giantBoolConective(m.getTag(), arity);
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
				
			case TagConstants.INTSHIFTRU:
				fn = symIntFn; tag = funUSR32; break;
			case TagConstants.INTSHIFTR:
				fn = symIntFn; tag = funASR32; break;
			case TagConstants.INTSHIFTL:
				fn = symIntFn; tag = funSL32; break;
				
			case TagConstants.LONGSHIFTRU:
				fn = symIntFn; tag = funUSR64; break;
			case TagConstants.LONGSHIFTR:
				fn = symIntFn; tag = funASR64; break;
			case TagConstants.LONGSHIFTL:
				fn = symIntFn; tag = funSL64; break;
				
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
					//ErrorSet.caution("Dttfsa " + op);
					return symbolRef(op);
				} else if (op.equals("identity")) {
					Assert.notFalse(arity == 3);
					Term body = transform((ASTNode)n.childAt(3));
					return body;
				} else {
					arity -= 2;
					fn = getFnSymbol(op, arity);
					Term[] args = new Term[arity];
					for (int i = 0; i < arity; ++i)
						args[i] = transform((ASTNode)n.childAt(i+3));
					return new FnTerm(fn, args); 
				}
			}
			
			case TagConstants.SUM:
				Assert.fail("sum unhandled"); break;
				
			case TagConstants.METHODCALL:
				ASTNode sym = m.symbol;
				fn = getFnSymbol(m.methodName.toString(), arity); 
				if (sym == null) {
					ErrorSet.caution("no symbol stored in methodCall: " + m.methodName);
				} else if (sym instanceof FieldDecl) {
					Assert.notFalse(arity <= 2);
					Sort ft = typeToSort(((FieldDecl)sym).type);
					if (arity == 0) {
						Sort s = registerMapSort(sortRef, ft);
						unify(fn.retType, s, "mc");
					} else {
						unify(fn.retType, ft, "mc1");
						for (int i = 0; i < fn.argumentTypes.length; ++i)
							unify(fn.argumentTypes[i], sortRef, "mca");
					}
				} else if (sym instanceof GenericVarDecl) {
					ErrorSet.caution("gvd in methodCall: " + m.methodName);
				} else if (sym instanceof MethodDecl) {
					MethodDecl md = (MethodDecl)sym;
					int off = arity - md.args.size(); 
					Assert.notFalse(off <= 2);
					for (int i = 0; i < arity; ++i) {
						Sort s = sortRef;
						if (i >= off)
							s = typeToSort(md.args.elementAt(i - off).type);
						unify(fn.argumentTypes[i], s, "mda");
					}
					unify(fn.retType, typeToSort(md.returnType), "mdr");									
				} else if (sym instanceof ConstructorDecl) {
					ConstructorDecl md = (ConstructorDecl)sym;
					int off = arity - md.args.size(); 
					Assert.notFalse(off <= 2);
					for (int i = 0; i < arity; ++i) {
						Sort s = sortTime;
						if (i >= off)
							s = typeToSort(md.args.elementAt(i - off).type);
						unify(fn.argumentTypes[i], s, "cda");
					}
					unify(fn.retType, sortRef, "mdr");
				} else {
					ErrorSet.error("unknown symbol stored in methodcall: " + sym.getClass());
				}
				//ErrorSet.caution("MethodCall " + fn);
				break;
				
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
			FnTerm res = new FnTerm(fn, args);
			res.tag = tag;
			
			return res;
			
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
				pats = new Term[1][];
				pats[0] = new Term[pats.length];
				for (int i = 0; i < pats.length; ++i)
					pats[0][i] = transform(m.pats.elementAt(i));
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
			
		} else if (n instanceof Type) { // javafe/Type
			Type t = (Type) n;
			return symbolRef(UniqName.type(t), sortType);
			
		} else if (n instanceof VariableAccess) {
			VariableAccess m = (VariableAccess) n;
			for (int i = 0; i < quantifiedVars.size(); ++i) {
				QuantVariable q = (QuantVariable)quantifiedVars.elementAt(i);
				if (q.var == m.decl)
					return new QuantVariableRef(q);
			}
			
			Sort s = null;
			String name = UniqName.variable(m.decl);
			
			GenericVarDecl decl = m.decl;
			
			while (decl instanceof LocalVarDecl && ((LocalVarDecl)decl).source != null)
				decl = ((LocalVarDecl)decl).source;				
			
			if (decl instanceof FieldDecl) {
				FieldDecl d = (FieldDecl)decl;
				if (Modifiers.isStatic(d.getModifiers()))
					s = typeToSort(d.type);
				else
					s = registerMapSort(sortRef, typeToSort(d.type));
				//ErrorSet.caution("VariableAccess " + name + " -> " + s);
			} else if (decl instanceof LocalVarDecl || decl instanceof FormalParaDecl) {
				GenericVarDecl g = (GenericVarDecl)decl;
				s = typeToSort(g.type);
				//ErrorSet.caution("VariableAccess local " + name + " -> " + s);
			} else {
				ErrorSet.caution("unknown decl in VariableAccess " + m.decl.getClass());
			}
			
			return symbolRef (name, s);
			
		} else {
			ErrorSet.fatal("unhandled tag " + TagConstants.toString(n.getTag()));
			return null;
		}
	}
	public Term transform(ASTNode n)
	{
		//ErrorSet.caution("enter " + TagConstants.toString(n.getTag()) + " " + n);
		Term t = doTransform(n);
		//ErrorSet.caution("exit " + TagConstants.toString(n.getTag()));
		return t;
	}

	/*@ non_null_by_default @*/
	public class SortedBackPred extends BackPred 
	{
		ArrayList axioms = new ArrayList();
		ArrayList distinct = new ArrayList();
		
		/**
		 * Return the type-specific background predicate as a formula.
		 */
		public void genTypeBackPred(FindContributors scope,
									PrintStream proverStream)
		{
			distinct.add(transform(Types.booleanType));
			distinct.add(transform(Types.charType));
			distinct.add(transform(Types.byteType));
			distinct.add(transform(Types.shortType));
			distinct.add(transform(Types.intType));
			distinct.add(transform(Types.longType));
			distinct.add(transform(Types.floatType));
			distinct.add(transform(Types.doubleType));
			distinct.add(transform(Types.voidType));
			distinct.add(transform(escjava.tc.Types.typecodeType));
						
			// Print them out, and add their contribution to the BP. 
			Info.out("[TypeSig contributors for "
					+Types.printName(scope.originType)+":");
			for( Enumeration typeSigs = scope.typeSigs();
			typeSigs.hasMoreElements(); )
			{
				TypeSig sig2 = (TypeSig)typeSigs.nextElement();
				Info.out("    "+Types.printName( sig2 ));
				addContribution( sig2.getTypeDecl(), proverStream );
				distinct.add(transform(sig2));
			}
			Info.out("]");
			
			// Handle constant fields' contribution:
			for( Enumeration fields = scope.fields();
			fields.hasMoreElements(); ) {
				FieldDecl fd = (FieldDecl)fields.nextElement();
				if (!Modifiers.isFinal(fd.modifiers) || fd.init==null)
					continue;
				
				int loc = fd.init.getStartLoc();
				VariableAccess f = VariableAccess.make(fd.id, loc, fd);
				
				if (Modifiers.isStatic(fd.modifiers)) {
					genFinalInitInfo(fd.init, null, null, f, fd.type, loc, 
							proverStream);
				} else {
					LocalVarDecl sDecl = UniqName.newBoundVariable('s');
					VariableAccess s = TrAnExpr.makeVarAccess(sDecl, Location.NULL);
					genFinalInitInfo(fd.init, sDecl, s, GC.select(f, s), fd.type, 
							loc, proverStream);
				}
			}
		}
		
		protected void produce(/*@ nullable @*/GenericVarDecl sDecl, /*@ nullable @*/Expr s,
				/*@ non_null */ Expr e,
				/*@ non_null */ PrintStream proverStream) {
			if (sDecl != null) {
				Expr ant = GC.nary(TagConstants.REFNE, s, GC.nulllit);
				ExprVec nopats = ExprVec.make(1);
				nopats.addElement(ant);
				e = GC.forall(sDecl, GC.implies(ant, e), nopats);
			}
			
			axioms.add(transform(e));
		}
		
		/**
		 * Add to b the contribution from a particular TypeDecl, which is
		 * a formula.
		 */
		
		protected void addContribution(/*@ non_null */ TypeDecl d,
				/*@ non_null */ PrintStream proverStream) {
			
			TypeSig sig = TypeCheck.inst.getSig(d);
			
			// === ESCJ 8: Section 1.1
			
			if( d instanceof ClassDecl ) {
				ClassDecl cd = (ClassDecl)d;
				
				if( cd.superClass != null ) {
					saySubClass( sig, cd.superClass, proverStream );
				}
				
				if( Modifiers.isFinal(cd.modifiers) )
					sayIsFinal( sig, proverStream );
				
			} else {
				saySubType( sig, Types.javaLangObject(), proverStream );
			}
			
			for( int i=0; i<d.superInterfaces.size(); i++ )
				saySubType( sig, d.superInterfaces.elementAt(i), proverStream );
			
			saySuper(d, proverStream);
		}
		
		
		FnTerm fn(FnSymbol f, Term a1)
		{
			return new FnTerm(f, new Term[] { a1 });
		}
		
		FnTerm fn(FnSymbol f, Term a1, Term a2)
		{
			return new FnTerm(f, new Term[] { a1, a2 });
		}
		
		void say(Term t)
		{
			axioms.add(t);
		}
		
		/** Record in the background predicate that x is a subclass of y. */
		
		private void saySubClass( Type x, Type y,
								  PrintStream proverStream ) 
		{
			saySubType( x, y, proverStream );
			Term tx = transform(x), ty = transform(y);
			say(fn(symAnyEQ, fn(symAsChild, tx, ty), tx));
		}
		
		/** Record in the background predicate that x is a subtype of y. */
		
		private void saySubType( Type x, Type y,
								PrintStream proverStream )
		{
			say(fn(symTypeLE, transform(x), transform(y)));
		}
		
		private void saySuper(TypeDecl d, /*@ non_null*/ PrintStream proverStream)
		{
			Expr sig = GC.typeExpr(TypeCheck.inst.getSig(d));
			
            LocalVarDecl boundVar = UniqName.newBoundVariable("t");
            Expr boundVarAccess = VariableAccess.make(boundVar.id, d.locId, boundVar);

            Expr subt = GC.nary(TagConstants.TYPEEQ, boundVarAccess, sig);
            
			if( d instanceof ClassDecl ) {
				ClassDecl cd = (ClassDecl)d;
				
				if( cd.superClass != null ) {
					subt = GC.or(subt,
							GC.nary(TagConstants.TYPELE, GC.typeExpr(cd.superClass), boundVarAccess));
				}
			} else {
				subt = GC.or(subt,
						GC.nary(TagConstants.TYPEEQ, GC.typeExpr(Types.javaLangObject()), 
													 boundVarAccess));
			}
			
			for( int i=0; i<d.superInterfaces.size(); i++ ) {
				subt = GC.or(subt,
						GC.nary(TagConstants.TYPELE, GC.typeExpr(d.superInterfaces.elementAt(i)), 
													 boundVarAccess));
			}
			
			Expr pat = GC.nary(TagConstants.TYPELE, sig, boundVarAccess); 
            Expr body = GC.nary(TagConstants.BOOLEQ, pat, subt);
			say(transform(GC.forallwithpats(boundVar,body, ExprVec.make(new Expr[] { pat }))));
		}
		
		/** Record in the background predicate that x is final. */
		
		private void sayIsFinal( Type x,
				/*@ non_null */ PrintStream proverStream ) 
		{
			Expr sig = GC.typeExpr(x);
			
            LocalVarDecl boundVar = UniqName.newBoundVariable("t");
            Expr boundVarAccess = VariableAccess.make(boundVar.id, x.getStartLoc(), boundVar);
            
			Expr pat = GC.nary(TagConstants.TYPELE, boundVarAccess, sig); 
            Expr body = GC.nary(TagConstants.BOOLEQ, pat, GC.nary(TagConstants.TYPEEQ, boundVarAccess, sig));
			say(transform(GC.forallwithpats(boundVar,body, ExprVec.make(new Expr[] { pat }))));
		}
		
	}

	// dump	
	/*@ nullable @*/EscNodeBuilder dumpBuilder;
	public static final Hashtable fnTranslations = new Hashtable();
	public static final ArrayList stringConstants = new ArrayList();
	public static final ArrayList distinctSymbols = new ArrayList();
	
	public static Sort[] mapSorts(EscNodeBuilder builder, Sort[] s)
	{
		Sort[] res = new Sort[s.length];
		for (int i = 0; i < s.length; ++i)
			res[i] = mapSortTo(builder, s[i]);
		return res;
	}
	
	public static SAny[] dumpArray(Term[] args)
	{
		SAny[] params = new SAny[args.length];
		for (int i = 0; i < args.length; ++i)
			params[i] = args[i].dumpAny();
		return params;
	}
	
	public static SPred[] dumpPredArray(Term[] args)
	{
		SPred[] params = new SPred[args.length];
		for (int i = 0; i < args.length; ++i)
			params[i] = args[i].dumpPred();
		return params;
	}
	
	public static STerm[] dumpTermArray(Term[] args)
	{
		STerm[] params = new SAny[args.length];
		for (int i = 0; i < args.length; ++i)
			params[i] = args[i].dump();
		return params;
	}
	
	public static Term toPred(Term body)
	{
		if (follow(body.getSort()) == sortBool)
			body = new FnTerm(symIsTrue, new Term[] { body });
		if (follow(body.getSort()) == sortValue)
			// TODO warning
			body = new FnTerm(symValueToPred, new Term[] { body });			
		unify(body.getSort(), sortPred, null);
		return body;		
	}
	
}
