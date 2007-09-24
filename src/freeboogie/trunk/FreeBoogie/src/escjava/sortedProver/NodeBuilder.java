package escjava.sortedProver;

import java.util.HashMap;
import java.util.HashSet;

/**
 * An interface that allows building a sorted query for a prover.
 * 
 * @author mjm
 * @author reviewed by TODO
 */
public abstract class NodeBuilder {
  public interface STerm {}

  public interface SPred extends STerm {}

  /* @ non_null_by_default @ */
  public interface SAny extends STerm {
    boolean isSubSortOf(Sort s);
  }

  public interface SMap extends SRef {}

  public interface SValue extends SAny {}

  public interface SBool extends SValue {}

  public interface SInt extends SValue {}

  public interface SReal extends SValue {}

  public interface SRef extends SValue {}

  // Arithmetic predicate IDs
  public final static int predFirst = 1;
  public final static int predEQ = predFirst;
  public final static int predNE = predEQ + 1;
  public final static int predLT = predNE + 1;
  public final static int predGT = predLT + 1;
  public final static int predLE = predGT + 1;
  public final static int predGE = predLE + 1;
  public final static int predLast = predGE;

  // Arithmetic function IDs
  public final static int funFirst = predLast + 1;
  public final static int funADD = funFirst;
  public final static int funSUB = funADD + 1;
  public final static int funMUL = funSUB + 1;
  public final static int funDIV = funMUL + 1;
  public final static int funMOD = funDIV + 1;
  public final static int funASR32 = funMOD + 1; // signed shift right
  public final static int funUSR32 = funASR32 + 1; // unsigned
  public final static int funSL32 = funUSR32 + 1;
  public final static int funASR64 = funSL32 + 1;
  public final static int funUSR64 = funASR64 + 1;
  public final static int funSL64 = funUSR64 + 1;
  public final static int funLast = funUSR64;

  // Unary arithmetic functions, I think that binary negation could also go here
  public final static int funUniFirst = funLast + 1;
  public final static int funNEG = funUniFirst;
  public final static int funUniLast = funNEG;
  public final static String[] tagsIds = { "Unknown", "predEQ", "predNE",
    "predLT", "predGT", "predLE", "predGE", "funADD", "funSUB", "funMUL",
    "funDIV", "funMOD", "funASR32", "funUSR32", "funSL32", "funASR64",
    "funUSR64", "funSL64", "funNEG" };

  private int currentSymbol = 1;

  public final Sort sortPred = registerSort("PRED", null);
  public final Sort sortAny = registerSort("any", null);
  public final Sort sortValue = registerSort("value", sortAny);
  public final Sort sortBool = registerSort("bool", sortValue);
  public final Sort sortInt = registerSort("int", sortValue);
  public final Sort sortReal = registerSort("real", sortValue);
  public final Sort sortRef = registerSort("ref", sortValue);
  public final Sort sortMap = registerSort("map", sortRef);
  public final Sort sortString = sortRef;

  protected HashMap<Integer, Symbol> fnSymbolsByTag = new HashMap<Integer, Symbol>();

  public final Sort[] emptySorts = new Sort[0];
  public final SAny[] emptyArgs = new SAny[0];

  public class Symbol {
    public final int id;
    public final String name;

    protected Symbol(String name) {
      this.name = name;
      this.id = currentSymbol++;
    }

    public boolean equals(Object o) {
      if (this == o) return true;
      if (o instanceof Symbol) {
        Symbol s = (Symbol)o;
        return name.equals(s.name);
      }
      return false;
    }

    public String toString() {
      return name;
    }
  }

  public class Sort extends Symbol {
    private final Sort superSort;
    private final Sort mapFrom;
    private final Sort mapTo;

    protected Sort(String name, Sort superSort, Sort mapFrom, Sort mapTo) {
      super(name);
      this.superSort = superSort;
      this.mapFrom = mapFrom;
      this.mapTo = mapTo;
    }

    public boolean equals(Object o) {

      return super.equals(o);
    }

    public boolean isSubSortOf(Sort other) {
      other = other.theRealThing();
      Sort th = theRealThing();
      if (th == other) return true;
      if (th.getSuperSort() == null) return false;
      return th.getSuperSort().isSubSortOf(other);
    }

    public Sort commonSuperSort(Sort other) {
      HashSet<Sort> h = new HashSet<Sort>();
      for (Sort s = this; s != null; s = s.getSuperSort())
        h.add(s);
      for (Sort s = other; s != null; s = s.getSuperSort())
        if (h.contains(s)) return s;
      return null;
    }

    public Sort getSuperSort() {
      return theRealThing().superSort;
    }

    public Sort getMapFrom() {
      return theRealThing().mapFrom;
    }

    public Sort getMapTo() {
      return theRealThing().mapTo;
    }

    public String toString() {
      if (getMapFrom() != null) return getSuperSort().name + "[" + getMapFrom()
        + "," + getMapTo() + "]";
      else return theRealThing().name;
    }

    public Sort theRealThing() {
      return this;
    }
  }

  public class QuantVar extends Symbol {
    public final Sort type;

    protected QuantVar(String name, Sort type) {
      super(name);
      this.type = type;
    }

    public String toString() {
      return "?" + name + " : " + type;
    }
  }

  public class FnSymbol extends Symbol {
    public final Sort[] argumentTypes;
    public final Sort retType;

    protected FnSymbol(String name, Sort[] args, Sort ret_type) {
      super(name);
      argumentTypes = args;
      retType = ret_type;
    }

    public String toString() {
      String s = name + " : (";
      for (int i = 0; i < argumentTypes.length; ++i) {
        if (i != 0) s += " * ";
        s += argumentTypes[i];
      }
      return s + ") -> " + retType;
    }
  }

  public class PredSymbol extends FnSymbol {
    protected PredSymbol(String name, Sort[] args) {
      super(name, args, sortPred);
    }
  }

  // Registration and generic stuff
  public Sort registerSort(String name, Sort superSort) {
    Sort s = new Sort(name, superSort, null, null);
    return s;
  }

  public Sort registerMapSort(Sort mapFrom, Sort mapTo, Sort superSort) {
    String name = superSort.name + "[" + mapFrom.name + "," + mapTo.name + "]";
    Sort s = new Sort(name, superSort, mapFrom, mapTo);
    return s;
  }

  public Sort registerMapSort(Sort mapFrom, Sort mapTo) {
    return registerMapSort(mapFrom, mapTo, sortMap);
  }

  /**
   * All the symbols are scoped by the push/isValid calls. All symbols
   * registered prior to push/isValid call, are assumed to be used only by the
   * formula passed there, and possibly by stuff further up the stack. In other
   * words, they become invalid after pop or the end of isValid call
   * respectively.
   * 
   * @param name
   * @param args
   */
  public PredSymbol registerPredSymbol(String name, Sort[] args) {
    return registerPredSymbol(name, args, 0);
  }

  public PredSymbol registerPredSymbol(String name, Sort[] args, int tag) {
    PredSymbol p = new PredSymbol(name, args);
    if (tag != 0) fnSymbolsByTag.put(new Integer(tag), p);
    return p;
  }

  // The names are only unique within a given formula to be checked.
  public FnSymbol registerFnSymbol(String name, Sort[] args, Sort ret_type) {
    return registerFnSymbol(name, args, ret_type, 0);
  }

  // @ requires \nonnullelements(args);
  public FnSymbol registerFnSymbol(String name, Sort[] args, Sort ret_type,
    int tag) {
    FnSymbol fn = new FnSymbol(name, args, ret_type);
    if (tag != 0) fnSymbolsByTag.put(new Integer(tag), fn);
    return fn;
  }

  public FnSymbol registerConstant(String name, Sort type) {
    return new FnSymbol(name, emptySorts, type);
  }

  public QuantVar registerQuantifiedVariable(String name, Sort type) {
    return new QuantVar(name, type);
  }

  abstract public SAny buildFnCall(FnSymbol fn, SAny[] args);

  abstract public SAny buildConstantRef(FnSymbol c);

  abstract public SAny buildQVarRef(QuantVar v);

  abstract public SPred buildPredCall(PredSymbol fn, SAny[] args);

  // Boolean connectives
  abstract public SPred buildImplies(SPred arg1, SPred arg2);

  abstract public SPred buildIff(SPred arg1, SPred arg2);

  abstract public SPred buildXor(SPred arg1, SPred arg2);

  abstract public SPred buildAnd(SPred[] args);

  abstract public SPred buildOr(SPred[] args);

  abstract public SPred buildNot(SPred arg);

  abstract public SPred buildTrue();

  abstract public SPred buildDistinct(SAny[] terms);

  /*
   * Possible translation is: if (positive) pred /\ P_name else pred \/ N_name
   * And then return as P_name if it's assigned true in the model and N_name if
   * it's assigned false. You need to return this stuff in
   * CounterExampleResponse class (without P_ or N_ of course).
   */
  abstract public SPred buildLabel(boolean positive, String name, SPred pred);

  abstract public SValue buildITE(SPred cond, SValue then_part, SValue else_part);

  abstract public SPred buildForAll(QuantVar[] vars, SPred body,
    STerm[][] pats, STerm[] nopats);

  abstract public SPred buildExists(QuantVar[] vars, SPred body);

  // Arithmetic
  abstract public SPred buildIntPred(int intPredTag, SInt arg1, SInt arg2);

  abstract public SInt buildIntFun(int intFunTag, SInt arg1, SInt arg2);

  abstract public SBool buildIntBoolFun(int intFunTag, SInt arg1, SInt arg2);

  abstract public SPred buildRealPred(int realPredTag, SReal arg1, SReal arg2);

  abstract public SBool buildRealBoolFun(int realPredTag, SReal arg1, SReal arg2);

  abstract public SReal buildRealFun(int realFunTag, SReal arg1, SReal arg2);

  abstract public SInt buildIntFun(int intFunTag, SInt arg1);

  abstract public SReal buildRealFun(int realFunTag, SReal arg1);

  // Literals
  abstract public SBool buildBool(boolean b);

  abstract public SInt buildInt(long n);

  abstract public SReal buildReal(double f);

  abstract public SRef buildNull();

  // we though about having buildString() here but we're not sure what the
  // semantics should be

  // Maps
  abstract public SValue buildSelect(SMap map, SValue idx);

  abstract public SMap buildStore(SMap map, SValue idx, SValue val);

  // Equality
  abstract public SPred buildAnyEQ(SAny arg1, SAny arg2);

  abstract public SPred buildAnyNE(SAny arg1, SAny arg2);

  // Type conversions
  abstract public SValue buildValueConversion(Sort from, Sort to, SValue val);

  abstract public SPred buildIsTrue(SBool val);

  // Mobius specific stuff
  abstract public SPred buildNewObject(SMap oldh, SAny type, SMap heap, SRef r);

  abstract public SAny buildSort(Sort s);

  abstract public SValue buildDynSelect(SMap map, SRef obj, SAny field);

  abstract public SMap buildDynStore(SMap map, SRef obj, SAny field, SValue val);

  abstract public SPred buildNewArray(SMap oldh, SAny type, SMap heap, SRef r,
    SInt len);

  abstract public SValue buildArrSelect(SMap map, SRef obj, SInt idx);

  abstract public SMap buildArrStore(SMap map, SRef obj, SInt idx, SValue val);

  abstract public SPred buildAssignCompat(SMap map, SValue val, SAny type);
}
