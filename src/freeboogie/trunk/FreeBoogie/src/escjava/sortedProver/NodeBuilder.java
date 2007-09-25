package escjava.sortedProver;

import java.util.HashSet;

/**
 * An interface that allows building a sorted query for a prover.
 * 
 * The user has some predefined sorts (the member variables sort*),
 * some predefined function symbols (the member variables fun*),
 * and some predefined predicate symbols (the member variables pred*).
 * These are
 * 
 * @author mjm
 * @author changed by rgrig
 */
public abstract class NodeBuilder {
  
  // === The interfaces for the query `AST'
  
  /** A term */
  public interface STerm { /* empty */ }

  /** A predicate is a boolean term. */
  public interface SPred extends STerm { /* empty */ }

  /** An untyped term. TODO: explain why it is different from STerm */
  public interface SAny extends STerm {
    /** 
     * Typed terms must be able to answer this question.
     * @param s the would-be super-sort of {@code this}
     * @return whether {@code s} is a super-sort of {@code this} 
     */
    boolean isSubSortOf(Sort s);
  }

  /** A value. */
  public interface SValue extends SAny { /* empty */ }

  /** A boolean. */
  public interface SBool extends SValue { /* empty */ }

  /** An integer. TODO: is this unbounded? */
  public interface SInt extends SValue { /* empty */ }

  /** A real number. TODO: is this floating point or real real? */
  public interface SReal extends SValue { /* empty */ }

  /** A reference. */
  public interface SRef extends SValue { /* empty */ }

  /** A map, used for example for arrays. */
  public interface SMap extends SRef { /* empty */ }

  // === The types for things that can be sent as `primitive' arguments
  // === to the build* methods

  /**
   * A symbol is basically a name, that has some meaning for the theorem
   * prover.
   */
  public class Symbol {
    /** The string representation of the symbol. */
    public final String name;

    /** Construct a new {@code Symbol}. */ 
    protected Symbol(String name) { this.name = name; }

    @Override
    public boolean equals(Object o) {
      if (this == o) return true;
      if (o instanceof Symbol) {
        Symbol s = (Symbol)o;
        return name.equals(s.name);
      }
      return false;
    }

    @Override
    public String toString() {
      return name;
    }
  }

  /**
   * A prover sort. (Something like a `type', but that would easily be
   * confused with the `type' in the programming language that for which
   * the verifier works.)
   * 
   * Note that there may be more than one sort with the same name.
   * (For example the name "<" is used both for integer comparison and
   * real numbers comparison.)
   *
   * @author mjm
   * @author changed by rgrig
   */
  public class Sort extends Symbol {
    private final Sort superSort;
    
    // For map sorts:
    private final Sort mapFrom;
    private final Sort mapTo;

    /**
     * Construct a new sort. Clients call {@code registerSort}
     * instead of seeing this constructor. This way subclasses of
     * {@code NodeBuilder} can do custom stuff by overriding
     * {@code registerSort}.
     * 
     * @param name a string representation of the sort
     *   (the one known by many provers, so that the corresponding
     *   {@code SortedProver} class doesn't have to special case printing it)
     * @param superSort the super sort
     * @param mapFrom what is mapped, {@code null} for non-mapping sorts
     * @param mapTo to what is mapped, {@code null} for non-mapping sorts
     */
    protected Sort(String name, Sort superSort, Sort mapFrom, Sort mapTo) {
      super(name);
      this.superSort = superSort;
      this.mapFrom = mapFrom;
      this.mapTo = mapTo;
    }

    @Override
    public boolean equals(Object o) {
      return super.equals(o);
    }

    /**
     * Checks the sub-sort relationship
     * @param other the possible super-sort
     * @return whether {@code other} is a (not necessarily immediate) super
     *   sort of {@code this}
     */
    public boolean isSubSortOf(Sort other) {
      if (this == other) return true;
      if (superSort == null) return false;
      return superSort.isSubSortOf(other);
    }

    /**
     * Finds the least common super sort.
     * 
     * @param other the sorts being compared are {@code this} and {@code other}
     * @return the least common super sort, or {@code null} if it doesn't exist
     */
    public Sort commonSuperSort(Sort other) {
      HashSet<Sort> h = new HashSet<Sort>();
      for (Sort s = this; s != null; s = s.superSort) h.add(s);
      for (Sort s = other; s != null; s = s.superSort)
        if (h.contains(s)) return s;
      return null;
    }

    /** @return the super sort of {@code this} */
    public Sort getSuperSort() { return superSort; }

    /** 
     * @return the domain of the map, or {@code null} if {@code this} 
     *   is not a map
     */
    public Sort getMapFrom() { return mapFrom; }

    /** 
     * @return the range of the map, or {@code null} if {@code this} 
     *   is not a map
     */
    public Sort getMapTo() { return mapTo; }

    @Override
    public String toString() {
      if (getMapFrom() != null) return getSuperSort().name + "[" + getMapFrom()
        + "," + getMapTo() + "]";
      else return name;
    }
  }

  /**
   * Creates a new sort.
   * @param name the name of the sort
   * @param superSort the super sort, or {@code null}
   * @return the new sort
   */
  public Sort registerSort(String name, Sort superSort) {
    Sort s = new Sort(name, superSort, null, null);
    return s;
  }

  /**
   * A quantified variable.
   *
   * @author mjm 
   * @author changed by rgrig
   */
  public class QuantVar extends Symbol {
    /** The (prover) sort of the variable. */
    public final Sort sort;

    /** 
     * Construct a quantified variable. Clients use 
     * {@code registerQuantifiedVariable}, which may be overriden
     * by sub-classes of {@code NodeBuilder}.
     * 
     * @param name the variable
     * @param sort the sort of the variable
     */
    protected QuantVar(String name, Sort sort) {
      super(name);
      this.sort = sort;
    }

    @Override
    public String toString() {
      return "?" + name + " : " + sort;
    }
  }

  /**
   * A function symbol.
   *
   * @author mjm 
   * @author changed by rgrig
   */
  public class FnSymbol extends Symbol {
    /** The sorts of the arguments. The arity is {@code argSorts.length}. */
    public final Sort[] argSorts;
    
    /** The sort of the return. */
    public final Sort retSort;

    /**
     * Construct a new function symbol. Clients use
     * {@code registerFnSymbol}, which may be overriden by sub-classes
     * of {@code NodeBuilder}.
     * 
     * @param name the string representation of the function
     * @param argSorts the sorts of the arguments
     * @param retSort the sort of the return value
     */
    protected FnSymbol(String name, Sort[] argSorts, Sort retSort) {
      super(name);
      this.argSorts = argSorts;
      this.retSort = retSort;
    }

    @Override
    public String toString() {
      String s = name + " : (";
      for (int i = 0; i < argSorts.length; ++i) {
        if (i != 0) s += " * ";
        s += argSorts[i];
      }
      return s + ") -> " + retSort;
    }
  }

  /**
   * Registers (creates) a new function symbol.
   * @param name the name of the function
   * @param argSorts the sorts of the arguments
   * @param retSort the sort of the return value
   * @return the created function symbol
   */
  public FnSymbol registerFnSymbol(String name, Sort[] argSorts, Sort retSort) {
    return new FnSymbol(name, argSorts, retSort);
  }

  /**
   * Registers (creates) a function of arity zero.
   * @param name the constant
   * @param sort the sort of the constant
   * @return the created constant
   */
  public FnSymbol registerConstant(String name, Sort sort) {
    return new FnSymbol(name, new Sort[0], sort);
  }

  /**
   * Registers (creates) a quantified variable. 
   * @param name the variable
   * @param sort its sort
   * @return the created quantified variable
   */
  public QuantVar registerQuantifiedVariable(String name, Sort sort) {
    return new QuantVar(name, sort);
  }

  /** The predicate sort. TODO: shouldn't it be a subsort of {@code sortAny}? */
  public final Sort sortPred = registerSort("PRED", null);
  
  /**
   * A predicate symbol.
   *
   * @author mjm 
   * @author changed by rgrig
   */
  public class PredSymbol extends FnSymbol {
    /**
     * Construct a new predicate symbol. Clients use the methods
     * {@code registerPredSymbol}, which may be overriden by sub-classes
     * of {@code NodeBuilder}.
     * 
     * @param name the name of the predicate
     * @param args the sorts of its arguments
     */
    protected PredSymbol(String name, Sort[] args) {
      super(name, args, sortPred);
    }
  }

  /**
   * Registers (creates) a new predicate.
   * @param name the predicate
   * @param argSorts the sorts of its arguments
   * @return the created predicate
   */
  public PredSymbol registerPredSymbol(String name, Sort[] argSorts) {
    return new PredSymbol(name, argSorts);
  }

  /**
   * Registers (creates) a new map sort.
   * @param mapFrom the domain
   * @param mapTo the range
   * @param superSort the super sort
   * @return the created sort
   */
  public Sort registerMapSort(Sort mapFrom, Sort mapTo, Sort superSort) {
    String name = superSort.name + "[" + mapFrom.name + "," + mapTo.name + "]";
    return new Sort(name, superSort, mapFrom, mapTo);
  }

  /**
   * Registers (creates) a new map sort (with no super sort).
   * @param mapFrom the domain
   * @param mapTo the range
   * @return the created sort
   */
  public Sort registerMapSort(Sort mapFrom, Sort mapTo) {
    return registerMapSort(mapFrom, mapTo, sortMap);
  }
  
  
  // === Sorts that appear in most provers
  
  /** The `any' sort. Also used for unsorted provers. */
  public final Sort sortAny = registerSort("any", null);
  
  /** The value sort. */
  public final Sort sortValue = registerSort("value", sortAny);
  
  /** The boolean sort */
  public final Sort sortBool = registerSort("bool", sortValue);
  
  /** The integer sort. */
  public final Sort sortInt = registerSort("int", sortValue);
  
  /** The real sort. */
  public final Sort sortReal = registerSort("real", sortValue);
  
  /** The reference sort. */
  public final Sort sortRef = registerSort("ref", sortValue);
  
  /** The map sort. TODO: what's this for? */
  public final Sort sortMap = registerSort("map", sortRef);
  
  /** The string sort is the same as the reference sort. */
  public final Sort sortString = sortRef;
  
  
  // === Predicates supported by most provers
  
  /** (Polimorphic) equality */
  public final PredSymbol predEq = 
    registerPredSymbol("==", new Sort[] {sortAny, sortAny});
  
  /** (Polymorphic) non-equality */
  public final PredSymbol predNe =
    registerPredSymbol("!=", new Sort[] {sortAny, sortAny});
  
  /** Integer less-than */
  public final PredSymbol predIntLt =
    registerPredSymbol("<", new Sort[] {sortInt, sortInt});
  
  /** Integer greater-than */
  public final PredSymbol predIntGt =
    registerPredSymbol(">", new Sort[] {sortInt, sortInt});
  
  /** Integer less-or-equal */
  public final PredSymbol predIntLe =
    registerPredSymbol("<=", new Sort[] {sortInt, sortInt});
  
  /** Integer greater-or-equal */
  public final PredSymbol predIntGe =
    registerPredSymbol(">=", new Sort[] {sortInt, sortInt});
  
  // === Functions supported by most provers

  /** The result of a function is something else than a `prover boolean'. */
  public enum Function {
    /** addition */ ADD,
    /** subtraction */ SUB,
    /** multiplication */ MUL,
    /** division */ DIV,
    /** modulo */ MOD,
    /** signed shift right on 32 bits */ ASR32,
    /** unsigned shift right on 32 bits */ LSR32,
    /** shift left on 32 bits */ SL32,
    /** signed shift right on 64 bits */ ASR64,
    /** unsigned shift right on 64 bits */ LSR64,
    /** shift left on 32 bits */ SL64,
    /** unary minus */ NEG
  }
  
  // === (Abstract) builders.

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
