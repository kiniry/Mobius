package mobius.sortedProver.lifter.members;

import mobius.sortedProver.Lifter;
import mobius.sortedProver.NodeBuilder;
import mobius.sortedProver.NodeBuilder.SBool;
import mobius.sortedProver.NodeBuilder.SMap;
import mobius.sortedProver.NodeBuilder.STerm;
import mobius.sortedProver.nodebuilder.members.FnSymbol;
import mobius.sortedProver.nodebuilder.members.PredSymbol;
import mobius.sortedProver.nodebuilder.members.Sort;
import javafe.util.Assert;
import javafe.util.ErrorSet;

/*@ non_null_by_default @*/
public class FnTerm extends Term
{
	int pass;
	public FnSymbol fn;
	final public Term[] args;
	public int tag;
	final public Sort retType;
	public boolean isStringConst;
	public boolean isDistinctSymbol;
	
	public FnTerm(FnSymbol fn, Term[] args)
	{
		this.fn = fn;
		this.args = args;
		if (fn == Lifter.symSelect || fn == Lifter.symStore || fn == Lifter.symAsField)
			retType = new SortVar();
		else
			retType = fn.retType;
	}
	
	public Sort getSort() { return retType; }
	
	void enforceArgType(int i, Sort r)
	{
		r = Lifter.follow(r);
		Sort p = Lifter.follow(args[i].getSort());
		
		if (isEarlySort (r, p))
			return;
		
		FnSymbol conv = null;
		
		int minpass = 2;
		if (p == Lifter.sortValue)
			conv =
				r == Lifter.sortInt ? Lifter.symValueToInt : 
				r == Lifter.sortRef ? Lifter.symValueToRef : 
				r == Lifter.sortBool ? Lifter.symValueToBool : 
				r == Lifter.sortPred ? Lifter.symValueToPred : // TODO flag this with warning
				r == Lifter.sortReal ? Lifter.symValueToReal :
				null;
		else if (p == Lifter.sortInt && r == Lifter.sortReal) {
			conv = Lifter.symIntToReal;
			minpass = 0;
		} else if (p == Lifter.sortPred && (r == Lifter.sortValue || r == Lifter.sortBool)) {
			conv = Lifter.symPredToBool;
			ErrorSet.caution("using pred -> bool conversion! in arg #" + (1+i) + " of " + fn + " / " + this);				
		} else if (p == Lifter.sortBool && r == Lifter.sortPred) {
			conv = Lifter.symIsTrue;
			minpass = 1;
		}
		
		if (pass >= minpass && conv != null) {
			args[i] = new FnTerm(conv, new Term[] { args[i] });
		} else if (!Lifter.require(p, r, args[i]))
			ErrorSet.error("which is arg #" + (1+i) + " of " + fn + " / " + this);
	}
	
	public void infer(int pass)
	{
		this.pass = pass;
		if (Lifter.doTrace)
			Lifter.trace("start infer " + pass + ": " + fn + " / " + this + " -> " + retType);
		
		if (args.length != fn.argumentTypes.length) {
			ErrorSet.error("wrong number of parameters to " + fn + " ---> " + this);
			return;
		}
		
		for (int i = 0; i < args.length; ++i)
			args[i].infer(pass);			
		
		boolean skip = pass < Lifter.lastPass;
		
		if (fn == Lifter.symSelect)
		{
			Sort idx = new SortVar();
			Sort map = Lifter.registerMapSort(idx, retType);
			
			enforceArgType(0, map);
			enforceArgType(1, idx);
		}
		else if (fn == Lifter.symStore)
		{
			Sort idx = new SortVar();
			Sort val = new SortVar();
			Sort map = Lifter.registerMapSort(idx, val);
			
			if (!isEarlySort(retType, map))
				Lifter.unify(retType, map, this);				
			enforceArgType(0, map);
			enforceArgType(1, idx);
			enforceArgType(2, val);
		}
		else if (fn == Lifter.symAnyEQ || fn == Lifter.symAnyNE) {
			Sort common = new SortVar();
			
			enforceArgType(0, common);
			enforceArgType(1, common);
			
			if (Lifter.follow(args[0].getSort()) == Lifter.sortPred ||
					Lifter.follow(args[1].getSort()) == Lifter.sortPred)
			{
				if (fn == Lifter.symAnyEQ)
					fn = Lifter.symIff;
				else
					fn = Lifter.symXor;
				skip = false;
			}
		}
		else if (fn == Lifter.symAsField) {
			Sort field = Lifter.registerMapSort(new SortVar(), new SortVar(), Lifter.sortField);
			
			enforceArgType(0, field);
			enforceArgType(1, Lifter.sortType);				
			Lifter.unify(field, retType, this);				
		}
		else if (fn == Lifter.symFClosedTime) {
			Sort field = Lifter.registerMapSort(new SortVar(), new SortVar(), Lifter.sortField);
			
			enforceArgType(0, field);				
		} else skip = false;
		
		if (!skip)
			for (int i = 0; i < args.length; ++i)
				enforceArgType(i, fn.argumentTypes[i]);					
		
		if (Lifter.doTrace)
			Lifter.trace("infer " + pass + ": " + fn + " / " + this + " -> " + retType);
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
	
	public STerm dump()
	{
		boolean isPred = Lifter.follow(fn.retType) == Lifter.sortPred;
		FnSymbol tfn = Lifter.mapFnSymbolTo(dumpBuilder, fn);
		if (tfn == null && Lifter.fnTranslations.containsKey(fn))
			tfn = (FnSymbol)Lifter.fnTranslations.get(fn);
			
		if (tfn != null)
			if (isPred)
				return dumpBuilder.buildPredCall((PredSymbol)tfn, Lifter.dumpArray(args));
			else
				return dumpBuilder.buildFnCall(tfn, Lifter.dumpArray(args));
		
		if (fn == Lifter.symImplies)
			return dumpBuilder.buildImplies(args[0].dumpPred(), args[1].dumpPred());
		if (fn == Lifter.symIff)
			return dumpBuilder.buildIff(args[0].dumpPred(), args[1].dumpPred());
		if (fn == Lifter.symXor)
			return dumpBuilder.buildXor(args[0].dumpPred(), args[1].dumpPred());
		if (fn == Lifter.symNot)
			return dumpBuilder.buildNot(args[0].dumpPred());
		if (fn.name == "%and")
			return dumpBuilder.buildAnd(Lifter.dumpPredArray(args));
		if (fn.name == "%or")
			return dumpBuilder.buildOr(Lifter.dumpPredArray(args));
		if (fn == Lifter.symTermConditional)
			return dumpBuilder.buildITE(args[0].dumpPred(), args[1].dumpValue(), args[2].dumpValue());
		if (fn == Lifter.symIntPred)
			return dumpBuilder.buildIntPred(tag, args[0].dumpInt(), args[1].dumpInt());
		if (fn == Lifter.symIntFn)
			return dumpBuilder.buildIntFun(tag, args[0].dumpInt(), args[1].dumpInt());
		if (fn == Lifter.symRealPred)
			return dumpBuilder.buildRealPred(tag, args[0].dumpReal(), args[1].dumpReal());
		if (fn == Lifter.symRealFn)
			return dumpBuilder.buildRealFun(tag, args[0].dumpReal(), args[1].dumpReal());			
		if (fn == Lifter.symIntegralNeg)
			return dumpBuilder.buildIntFun(Lifter.funNEG, args[0].dumpInt());
		if (fn == Lifter.symFloatingNeg)
			return dumpBuilder.buildRealFun(Lifter.funNEG, args[0].dumpReal());
		if (fn == Lifter.symSelect)
			return dumpBuilder.buildSelect((SMap)args[0].dump(), args[1].dumpValue());
		if (fn == Lifter.symStore)
			return dumpBuilder.buildStore((SMap)args[0].dump(), args[1].dumpValue(), args[2].dumpValue());
		
		if (fn == Lifter.symAnyEQ || fn == Lifter.symAnyNE) {
			Sort t1 = args[0].getSort().theRealThing();
			Sort t2 = args[1].getSort().theRealThing();
			
			int tag = fn == Lifter.symAnyEQ ? Lifter.predEQ : Lifter.predNE;

			if (t1.isSubSortOf(Lifter.sortInt) && t2.isSubSortOf(Lifter.sortInt))
				return dumpBuilder.buildIntPred(tag, args[0].dumpInt(), args[1].dumpInt());
			
			if (t1.isSubSortOf(Lifter.sortReal) && t2.isSubSortOf(Lifter.sortReal))
				return dumpBuilder.buildRealPred(tag, args[0].dumpReal(), args[1].dumpReal());
			
			if (fn == Lifter.symAnyEQ)
				return dumpBuilder.buildAnyEQ(args[0].dumpAny(), args[1].dumpAny());
			else
				return dumpBuilder.buildAnyNE(args[0].dumpAny(), args[1].dumpAny());				
		}
		
		if (fn == Lifter.symIsTrue)
			return dumpBuilder.buildIsTrue(args[0].dumpBool());
		
		if (fn == Lifter.symValueToPred)
			return dumpBuilder.buildIsTrue(
					(SBool)dumpBuilder.buildValueConversion(
							dumpBuilder.sortValue, dumpBuilder.sortBool, 
							args[0].dumpValue()));
		
		if (fn == Lifter.symPredToBool)
			return dumpBuilder.buildITE(args[0].dumpPred(),
					dumpBuilder.buildBool(true),
					dumpBuilder.buildBool(false));
		
		if (fn == Lifter.symValueToBool || fn == Lifter.symValueToInt || fn == Lifter.symValueToReal ||
			fn == Lifter.symValueToRef || fn == Lifter.symIntToReal)
			return dumpBuilder.buildValueConversion(Lifter.mapSortTo(dumpBuilder, fn.argumentTypes[0]),
					Lifter.mapSortTo(dumpBuilder, fn.retType), args[0].dumpValue());
		
		Assert.notFalse(! fn.name.startsWith("%"));
		
		tfn = isPred ? dumpBuilder.registerPredSymbol(fn.name, Lifter.mapSorts(dumpBuilder, fn.argumentTypes)) :
					   dumpBuilder.registerFnSymbol(fn.name, Lifter.mapSorts(dumpBuilder, fn.argumentTypes), 
							   Lifter.mapSortTo(dumpBuilder, fn.retType));
		Lifter.fnTranslations.put(fn, tfn);
		if (isStringConst) Lifter.stringConstants.add(this);
		if (isDistinctSymbol) Lifter.distinctSymbols.add(this);
		return dump();			
	}
	
	public void enforceLabelSense(int sense)
	{
		if (fn == Lifter.symNot)
			args[0].enforceLabelSense(-sense);
		else if (fn == Lifter.symImplies) {
			args[0].enforceLabelSense(-sense);
			args[1].enforceLabelSense(sense);
		} else if (fn == Lifter.symXor || fn == Lifter.symIff) {
			args[0].enforceLabelSense(0);
			args[1].enforceLabelSense(0);
		} else {
			for (int i = 0; i < args.length; ++i)
				args[i].enforceLabelSense(sense);
		}
	}
	boolean isEarlySort(Sort s, Sort p)
	{
		return isEarlySort( s) || isEarlySort( p);
	}
	
	boolean isEarlySort(Sort s)
	{
		s = Lifter.follow(s);
		
		if (pass == 0)
			return s == Lifter.sortAny || s == Lifter.sortPred || s == Lifter.sortValue || s == Lifter.sortRef;
		else if (pass == 1)
			return s == Lifter.sortAny || s == Lifter.sortPred || s == Lifter.sortValue;
		else if (pass == 2)
			return s == Lifter.sortAny || s == Lifter.sortPred;
		else
			return false;
	}
}