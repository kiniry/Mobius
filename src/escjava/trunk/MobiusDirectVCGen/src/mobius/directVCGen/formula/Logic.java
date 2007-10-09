package mobius.directVCGen.formula;


import java.util.HashSet;
import java.util.Iterator;
import java.util.Properties;
import java.util.Set;

import mobius.directVCGen.formula.jmlTranslator.struct.GlobalProperties;

import javafe.ast.GenericVarDecl;
import javafe.ast.VariableAccess;

import escjava.sortedProver.Lifter;
import escjava.sortedProver.NodeBuilder;
import escjava.sortedProver.Lifter.FnTerm;
import escjava.sortedProver.Lifter.QuantTerm;
import escjava.sortedProver.Lifter.QuantVariable;
import escjava.sortedProver.Lifter.QuantVariableRef;
import escjava.sortedProver.Lifter.Term;
import escjava.sortedProver.NodeBuilder.PredSymbol;
import escjava.sortedProver.NodeBuilder.Sort;


/**
 * The library to represents all the formulas that are predicates.
 * The safe formulas are more bullet proofs than the normal ones 
 * (they basically give less warnings and do more things). They should
 * be used seldomly.
 * @author J. Charles (julien.charles@inria.fr), H. Lehner
 */
public final class Logic {

  /** the sort to represent the predicates. */
  public static Sort sort = Formula.lf.sortPred;

  /**
   * @deprecated
   */
  private Logic() {
    
  }
  
  /**
   * Build a predicate term from two predicate terms.
   * @param f1 the left hand side part of the predicate
   * @param f2 the right hand side part of the predicate
   * @param sym the symbol associated, which gives its meaning to
   * the predicate
   * @return a well formed binary op
   */
  private static Term logicBinaryOp(final Term f1, final Term f2, final PredSymbol sym) {
    if ((!f1.getSort().equals(sort) || !f2.getSort().equals(sort))) {
      throw new IllegalArgumentException("Bad type. Expecting predicates, " +
                                         "found: " + f1.getSort() + " and " + f2.getSort());
    }
    return Formula.lf.mkFnTerm(sym, new Term[]{f1, f2});
  }

  /**
   * Build a unary predicate. 
   * @param f the term to wrap in the predicate
   * @param sym the symbol which gives its meaning to the predicate
   * @return a well formed unary op
   */
  private static Term logicUnaryOp(final Term f, final PredSymbol sym) {
    if (f.getSort() != sort) {
      throw new IllegalArgumentException("Bad type. Expecting predicate, " +
                                         "found: " + f.getSort());
    }
    return Formula.lf.mkFnTerm(sym, new Term []{f});
  }

  /**
   * Creates binary operation terms over numerical elements.
   * @param l the left hand side element of the binary
   * @param r the right hand side element of the binary
   * @param tag the tag defining the operation
   * @return a new numerical term
   */
  private static Term numBinaryOp(final Term l, final Term r, final int tag) {
    Term left = l;
    Term right = r;
    if (l.getSort() != r.getSort() ||
        (!Num.isNum(l.getSort()) || !Num.isNum(r.getSort()))) {
      throw new IllegalArgumentException("The sort of " + l + 
                                         " is different from the sort of " + r + ".");
    }
    FnTerm t = null;
    if (l.getSort() == Num.sortInt) {
      if (r.getSort() == Num.sortReal) {
        left = Num.intToReal(l);
        t = Formula.lf.mkFnTerm(Formula.lf.symRealPred, new Term[] {left, right});
      }
      else {
        t = Formula.lf.mkFnTerm(Formula.lf.symIntPred, new Term[] {left, right});
      }

    }
    else if (l.getSort() == Num.sortReal) {
      if (r.getSort() == Num.sortInt) {
        right = Num.intToReal(r);
      }
      t = Formula.lf.mkFnTerm(Formula.lf.symRealPred, new Term[] {left, right});
    }
    else {
      throw new IllegalArgumentException("The sort " + l.getSort() + " is invalid!"); 
    }
    t.tag = tag;
    return t;
  }

  /** 
   * The true of type prop.
   */
  public static Term True() {
    return Formula.lf.mkPredLiteral(true);
  }

  /** 
   * The false of type prop.
   */
  public static Term False() {
    return Formula.lf.mkPredLiteral(false);
  }

  /**
   * Create a BoolPred object, a conversion from a boolean object
   * to a predicate object if necessary.
   * @param e the boolean object to convert
   * @return the BoolPred conversion object
   */
  public static Term boolToPred(final Term e) {
    if (e.getSort() == Bool.sort) {
      return Formula.lf.mkFnTerm(Formula.lf.symIsTrue, new Term[] {e});
    }
    else if (e.getSort() == Logic.sort) {
      return e;
    }
    else {
      throw new IllegalArgumentException("Bad type when creating BoolProp, " +
                                         "found: " + e.getSort());
    }
  }

  /**
   * Create a And in the prop territory, from 2 booleans or
   * 2 properties. The 2 arguments should not have different types
   * or bad types (other than prop).
   * @param f1 The first argument of the and, of type Prop
   * @param f2 The second argument of the and, of type Prop
   * @return a newly created and connector
   */
  public static Term and(final Term f1, final Term f2) {
    return logicBinaryOp(f1, f2, Formula.lf.symAnd);
  }


  /**
   * All the methods in this library are 'safe':
   * no exception is thrown if the terms given to the methods
   * are boolean instead of pred, even better they are converted 
   * to pred.
   */
  public static final class Safe {
    /**
     * Create a And in the prop territory, from 2 booleans or
     * 2 properties. The 2 arguments should not have different types.
     * @see Logic#and(Term, Term)
     * @param f1 The first argument of the and, of type Prop
     * @param f2 The second argument of the and, of type Prop
     * @return a newly created and connector
     */
    public static Term and(final Term f1, final Term f2) {
      Term left = f1, right = f2;
      if (f1.getSort().equals(Bool.sort)) {
        left = Logic.boolToPred(f1);
      }
      if (f2.getSort().equals(Bool.sort)) {
        right = Logic.boolToPred(f1);
      }
      return Logic.and(left, right);
    }

    /**
     * Create an object representing a logical implies.
     * @see Logic#implies(Term, Term)
     * @param f1 the first element of the implies
     * @param f2 the second element of the implies
     * @return a nicely created implies
     */
    public static Term implies(final Term f1, final Term f2) {
      Term left = f1, right = f2;
      if (f1.getSort().equals(Bool.sort)) {
        left = Logic.boolToPred(f1);
      }
      if (f2.getSort().equals(Bool.sort)) {
        right = Logic.boolToPred(f2);
      }
      return Logic.implies(left, right);
    }
  }


  /**
   * Create an object representing an Or.
   * @param f1 the left parameter of the or
   * @param f2 the right parameter of the or
   * @return the newly created object
   */
  public static Term or(final Term f1, final Term f2) {
    return logicBinaryOp(f1, f2, Formula.lf.symOr);
  }


  /**
   * Creates and returns the negation of a formula.
   * @param f the formula to negate (of type prop)
   * @return return the new not construct
   */
  public static Term not(final Term f) {
    return logicUnaryOp(f, Formula.lf.symNot);
  }

  /**
   * Create an equals object; it has 2 arguments, and
   * they must have the same type.
   * @param l the left argument
   * @param r the right argument
   * @return an equal object
   */
  public static Term equals(final Term l, final Term r) {
    Term left = l;
    Term right = r;
    
    if ((l.getSort() == Formula.sort) | (r.getSort() == Formula.sort)) {
      return Formula.lf.mkFnTerm(Formula.lf.symAnyEQ, new Term[]{left, right});
    }
    
    if (l.getSort() != r.getSort() && 
        (!Num.isNum(r.getSort()) || !Num.isNum(l.getSort()))) {
      throw new IllegalArgumentException("Different types when creating equals, " +
                                         "found: " + l.getSort() + " and " + r.getSort());
    }
    
    FnTerm t = null;
    if ((l.getSort() == Bool.sort)) {
      t = Formula.lf.mkFnTerm(Formula.lf.symBoolPred, new Term[] {left, right});
      t.tag = NodeBuilder.predEQ;
    }
    if ((l.getSort() == Ref.sort)) {
      t = Formula.lf.mkFnTerm(Formula.lf.symRefEQ, new Term[] {left, right});
    }
    else if (l.getSort() == Num.sortInt) {
      if (r.getSort() == Num.sortReal) {
        left = Num.intToReal(l);
        t = Formula.lf.mkFnTerm(Formula.lf.symRealPred, new Term[] {left, right});
        t.tag = NodeBuilder.predEQ;
      }
      else {
        t = Formula.lf.mkFnTerm(Formula.lf.symIntPred, new Term[] {left, r});
        t.tag = NodeBuilder.predEQ;
      }
    }
    else if (l.getSort() == Num.sortReal) {
      if (r.getSort() == Num.sortInt) {
        right = Num.intToReal(r);
      }
      t = Formula.lf.mkFnTerm(Formula.lf.symRealPred, new Term[] {left, right});
      t.tag = NodeBuilder.predEQ;
    }
    else {
      t = Formula.lf.mkFnTerm(Formula.lf.symAnyEQ, new Term[]{left, right});
    }
    return  t;
  }

  /**
   * Create an object representing a logical implies.
   * @param f1 the first element of the implies
   * @param f2 the second element of the implies
   * @return a nicely created implies
   */
  public static Term implies(final Term f1, final Term f2) {
    return logicBinaryOp(f1, f2, Formula.lf.symImplies);
  }

  /**
   * Create an object representing a logical full implies.
   * @param f1 the first element of the full implies
   * @param f2 the second element of the full implies
   * @return a nicely created fullimplies
   */
  public static Term fullImplies(final Term f1, final Term f2) {
    return logicBinaryOp(f1, f2, Formula.lf.symIff);
  } 

  /**
   * Creates a universal binding for only one variable from the formula f.
   * @param v the variable to bind
   * @param f the formula which is the body of the forall
   * @return the forall construct newly created
   */
  public static QuantTerm forall(final QuantVariable v, final Term f) {

    if (f.getSort() != sort) {
      throw new IllegalArgumentException("Bad type when creating forall, " +
                                         "found: " + f.getSort());
    }
    return Formula.lf.mkQuantTerm(true, new QuantVariable [] {v}, f, null, null);
  }

  /**
   * Creates a universal binding for only one variable from the formula f.
   * @param v a reference to the variable to bind
   * @param f the formula which is the body of the forall
   * @return the forall construct newly created
   */
  public static QuantTerm forall(final QuantVariableRef v, final Term f) {

    if (f.getSort() != sort) {
      throw new IllegalArgumentException("Bad type when creating forall, " +
                                         "found: " + f.getSort());
    }
    return Formula.lf.mkQuantTerm(true, new QuantVariable [] {v.qvar}, f, null, null);
  }
  
  
  /**
   * Creates a universal binding for several vars from the formula f.
   * @param v the variable to bind
   * @param f the formula which is the body of the forall
   * @return the forall construct newly created
   */
  public static QuantTerm forall(final QuantVariable[] v, final Term f) {

    if (f.getSort() != sort) {
      throw new IllegalArgumentException("Bad type when creating forall, " +
                                         "found: " + f.getSort());
    }

    return Formula.lf.mkQuantTerm(true, v, f, null, null);
  }

  /**
   * Creates a existential binding for only one variable from the formula f.
   * @param v the variable to bind
   * @param f the formula which is the body of the forall
   * @return the forall construct newly created
   */
  public static QuantTerm exists(final QuantVariable v, final Term f) {

    if (f.getSort() != sort) {
      throw new IllegalArgumentException("Bad type when creating exists, " +
                                         "found: " + f.getSort());
    }

    return Formula.lf.mkQuantTerm(false, new QuantVariable [] {v}, f, null, null);
  }

  /**
   * Creates a existential binding for several vars from the formula f.
   * @param v the variable to bind
   * @param f the formula which is the body of the forall
   * @return the forall construct newly created
   */
  public static QuantTerm exists(final QuantVariable[] v, final Term f) {

    if (f.getSort() != sort) {
      throw new IllegalArgumentException("Bad type when creating exists, " +
                                         "found: " + f.getSort());
    }

    return Formula.lf.mkQuantTerm(false, v, f, null, null);
  }



  /**
   * Returns a boolean le expression.
   * @param l The left element of the expression
   * @param r The right expression of the expression
   * @return The and expression a FnTerm with tag {@link NodeBuilder#predLE}
   */
  public static Term le(final Term l, final Term r) {
    return numBinaryOp(l, r, NodeBuilder.predLE);
  }

  /**
   * Returns a boolean lt expression.
   * @param l The left element of the expression
   * @param r The right expression of the expression
   * @return The and expression a FnTerm with tag {@link NodeBuilder#predLE}
   */
  public static Term lt(final Term l, final Term r) {
    return numBinaryOp(l, r, NodeBuilder.predLT);
  }

  /**
   * Returns a boolean ge expression.
   * @param l The left element of the expression
   * @param r The right expression of the expression
   * @return The and expression a FnTerm with tag {@link NodeBuilder#predLE}
   */
  public static Term ge(final Term l, final Term r) {
    return numBinaryOp(l, r, NodeBuilder.predGE);
  }

  /**
   * Returns a boolean gt expression.
   * @param l The left element of the expression
   * @param r The right expression of the expression
   * @return The and expression a FnTerm with tag {@link NodeBuilder#predLE}
   */
  public static Term gt(final Term l, final Term r) {
    return numBinaryOp(l, r, NodeBuilder.predGT);
  }


  /**
   * Returns a predicate which is the test of the equality to zero
   * of the specified term.
   * @param t the term to equal to zero
   * @return a newly created predicate of the form (t == 0)
   */
  public static Term equalsZero(final Term t) {
    Term res = null;
    if (t.getSort() == Num.sortInt) {
      res = equals(t, Num.value(new Integer(0)));
    }
    else if (t.getSort() == Num.sortReal) {
      res = equals(t, Num.value(new Float(0)));
    }
    else {
      throw new IllegalArgumentException("The sort " + t.getSort() + " is invalid!"); 
    }
    return res;
  }

  /**
   * Returns a predicate that equals the given parameter to 
   * <code>null</code>. It returns something of the form
   * <code>t == null</code>.
   * @param t the parameter to equals to <code>null</code>
   * @return the predicate that equals <code>t</code> to 
   * <code>null</code>
   */
  public static Term equalsNull(final Term t) {
    Term res = null;
    if (t.getSort() == Ref.sort) {
      res = equals(t, Ref.Null());
    }
    else {
      throw new IllegalArgumentException("The sort " + t.getSort() + " is invalid!"); 
    }
    return res;
  }

  /**
   * Builds the term that represents the interval:
   * <code>0 &le; idx /\ idx &lt; dim</code>. It is
   * mainly used for array building.
   * @param dim the max dimension
   * @param idx the index that is within the interval
   * @return a term representing an index within an interval
   */
  public static Term interval0To(final Term dim, final QuantVariableRef idx) {
    if ((!dim.getSort().equals(Num.sortInt)) || 
        (!idx.getSort().equals(Num.sortInt))) {
      throw new IllegalArgumentException("The sort " + dim.getSort() + " or " +
                                         idx.getSort() +
                                         " is invalid! (Hint: should be int...)");
    }
    return Logic.and(Logic.le(Num.value(0), idx), Logic.lt(idx, dim));
  }

  /**
   * Builds a term that represents a subtype relation.
   * @param t1 the first type
   * @param t2 the second type to compare
   * @return a predicate that represents a subtype relation
   */
  public static FnTerm typeLE(final Term t1, final Term t2) {
    if (!t1.getSort().equals(Type.sort) || !t2.getSort().equals(Type.sort)) {
      throw new IllegalArgumentException("The given sorts were bad... it should be " +
                                         "types, found " + t1.getSort() + 
                                         " and " + t2.getSort());
    }
    return Formula.lf.mkFnTerm(Formula.lf.symTypeLE, new Term[] {t1, t2});
  }

  /**
   * Create the predicate that tells if a value is compatible with a specific type.
   * @param heap the current heap
   * @param val the value to check
   * @param type the type to check
   * @return the newly formed predicate
   */
  public static Term assignCompat(final Term heap, final Term val, final Term type) {
    if (heap.getSort() != Heap.sort) {
      throw new IllegalArgumentException("Type of the first param should be heap (" + 
                                         Heap.sort + "), found: " + heap.getSort());
    }
    if (type.getSort() != Type.sort) {
      throw new IllegalArgumentException("Type of the second param should be ref (" + 
                                         Type.sort + "), found: " + type.getSort());
    }
    return Formula.lf.mkFnTerm(Formula.lf.symAssignCompat, new Term [] {heap, val, type});
  }


  /**
   * @param x The object for which we want to get the invariant.
   * @param t The type where the invariant is defined.
   * @return A Predicate 'inv' representing an invariant of type t for object x.
   */
  public static Term inv(final Term heap, final Term x, final Term t) {
    return Formula.lf.mkFnTerm(Formula.lf.symInv, new Term[]{heap, x, t});
  }


  /**
   * @param heap Heap for which we want to know whether or not val is alive.
   * @param val The object in question.
   * @return A Term that expresses the predicate isAlloc(heap,val)
   */
  public static Term isAlive(final Term heap, final Term val) {
    if (heap.getSort() != Heap.sort) {
      throw new IllegalArgumentException("Type of the first param should be heap (" + 
                                         Heap.sort + "), found: " + heap.getSort());
    }
    return Formula.lf.mkFnTerm(Formula.lf.symIsAlive, new Term [] {heap, val});
  }



  /**
   * @param var The object for which we want to find out whether it could
   * have been modified by the method.
   * @param o Parameter object also containing a list of motifiable types.
   * @return A Term expressing the check described above.
   */
  public static Term isVisibleIn(final Term var, final GlobalProperties o) {
    Term t1 = null;
    Term t2 = null;
    final Set typeSet = o.visibleTypeSet;
    final Iterator iter = typeSet.iterator();

    while (iter.hasNext()) {
      final javafe.ast.Type type = (javafe.ast.Type) iter.next();
      final QuantVariableRef typeTerm = Type.translate(type);
      t1 = Logic.equals(var, typeTerm);
      if (t2 == null) {
        t2 = t1;
      }
      else {
        t2 = Logic.or(t2, t1);
      }
    }
    return t2;
  }

  /**
   * @param heap the current heap
   * @param targetVar the object containing fieldVar
   * @param fieldVar field of object targetVar
   * @return A term expressing the field "fieldVar" is of object "targetVar"
   */
  public static Term isFieldOf(final QuantVariableRef heap, final QuantVariableRef targetVar, final QuantVariableRef fieldVar) {
    if (heap.getSort() != Heap.sort) {
      throw new IllegalArgumentException("Type of the first param should be heap (" + 
                                         Heap.sort + "), found: " + heap.getSort());
    }
    return Formula.lf.mkFnTerm(Formula.lf.symIsFieldOf, new Term [] {heap, targetVar, fieldVar});
  }

  /**
   * @param targetVar the object containing the fieldVar
   * @param fieldVar the field for which we want to find out whether it's assignable or not
   * @param o Parameter object also containing a list of modifiable types.
   * @return A Term expressing the check described above.
   */
  public static Term isAssignable(final  Term targetVar, final QuantVariableRef fieldVar, final Object o) {
    Term t1 = null;
    Term t2 = null;
    final Set assignSet = (HashSet<QuantVariableRef[]>) ((Properties)o).get("assignableSet");
    final Iterator iter = assignSet.iterator();
    
    while (iter.hasNext()) {
      final QuantVariableRef[] setVar = (QuantVariableRef[]) iter.next();
      // FIXME jgc: here there is a type mistake fieldVar.qvar is supposed to be the name of the field, not a variable ref or fieldVar if you prefer
      //t1 = Logic.equals(Heap.loc(Heap.var, targetVar, fieldVar.qvar), Heap.loc(Heap.var, setVar[0], setVar[1].qvar));
      // FIXME claudia/ Hermann : fix this!
      t1 = Logic.equals(fieldVar, setVar[1]);
      if (t2 == null) {
        t2 = t1;
      }
      else {
        t2 = Logic.or(t2, t1);
      }
    }
    return t2;
  }
  

  /**
   * Main for testing purpose.
   * @param args ignored
   */
  public static void main(final String [] args) {
    final QuantVariable [] vars = {Expression.var("v1", Logic.sort),
                                   Expression.var("v2", Bool.sort) };

    final QuantVariableRef rv1 = Expression.rvar(vars[0]);
    final QuantVariableRef rv2 = Expression.rvar(vars[1]);
    final Term formula = 
      Logic.forall(vars, Logic.implies(rv1, rv2));
    System.out.println(formula);
    System.out.println(formula.subst(rv2,
                                     Logic.implies(Logic.boolToPred(rv2), 
                                                   Logic.False())));
    System.out.println(Logic.and(Logic.True(), Logic.False()));
  }


}
