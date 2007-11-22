package mobius.directVCGen.formula;

import escjava.sortedProver.NodeBuilder;
import escjava.sortedProver.Lifter.FnTerm;
import escjava.sortedProver.Lifter.Term;
import escjava.sortedProver.NodeBuilder.Sort;

/**
 * This library contains all the operations using integers and reals
 * returning an integer or a real.
 * @author J. Charles (julien.charles@inria.fr), H. Lehner
 */
public final class Num {
  /** the sort that represents integers. */
  public static Sort sortInt = Formula.lf.sortInt;
  /** the sort that represents real numbers. */
  public static Sort sortReal = Formula.lf.sortReal;

  /**
   * @deprecated
   */
  private Num() {
    
  }
  /**
   * Build a term that represents the given value.
   * @param l the numerical constant to translate to a term
   * @return a newly formed term representing the given constant
   */
  public static Term value(final Long l) {
    return Formula.lf.mkIntLiteral(l);
  }

  /**
   * Build a term that represents the given value.
   * @param i the numerical constant to translate to a term
   * @return a newly formed term representing the given constant
   */
  public static Term value(final Integer i) {
    return Formula.lf.mkIntLiteral(i.longValue());
  }

  /**
   * Build a term that represents the given value.
   * @param b the numerical constant to translate to a term
   * @return a newly formed term representing the given constant
   */
  public static Term value(final Byte b) {
    return Formula.lf.mkIntLiteral(b.longValue());
  }

  /**
   * Build a term that represents the given value.
   * @param s the numerical constant to translate to a term
   * @return a newly formed term representing the given constant
   */
  public static Term value(final Short s) {
    return Formula.lf.mkIntLiteral(s.longValue());
  }

  /**
   * Build a term that represents the given value.
   * @param f the numerical constant to translate to a term
   * @return a newly formed term representing the given constant
   */
  public static Term value(final Float f) {
    return Formula.lf.mkRealLiteral(f.doubleValue());
  }

  /**
   * Build a term that represents the given value.
   * @param c the numerical constant to translate to a term
   * @return a newly formed term representing the given constant
   */
  public static Term value(final Character c) {
    return Formula.lf.mkIntLiteral(c.charValue());
  }

  /**
   * Build a term that represents the given value.
   * @param d the numerical constant to translate to a term
   * @return a newly formed term representing the given constant
   */
  public static Term value(final Double d) {
    return Formula.lf.mkRealLiteral(d);
  }

  /**
   * Build an arithmetic operation from the given terms.
   * It is tipically a binary op. It does all the necessary conversions
   * to real if needed.
   * @param l the left element of the op
   * @param r the right element of the op
   * @param tag a valid tag (see {@link NodeBuilder#tagsIds})
   * @return a valid term of a numerical operation
   */
  private static Term arith(final Term l, final Term r, final int tag) {
    Term left = l;
    Term right = r;
    if (l.getSort() != r.getSort() && 
        (!Num.isNum(r.getSort()) || !Num.isNum(l.getSort()))) {
      throw new IllegalArgumentException("The sort of " + l + 
                                         " is different from the sort of " + r + ".");
    }
    FnTerm t = null;
    if (l.getSort() != r.getSort()) {
      if (l.getSort() == Num.sortInt) {
        left = Num.intToReal(l);
      }
      else {
        right = Num.intToReal(r);
      }
    }
    if (l.getSort() == Num.sortInt) {
      t = Formula.lf.mkFnTerm(Formula.lf.symIntFn, new Term[] {left, right});
      t.tag = tag;
    }
    else if (l.getSort() == Num.sortReal) {
      t = Formula.lf.mkFnTerm(Formula.lf.symRealFn, new Term[] {left, right});
      t.tag = tag;
    }
    else {
      throw new IllegalArgumentException("The sort " + l.getSort() + " is invalid!"); 
    }
    return t;
  }




  /**
   * Create an object representing an integer addition.
   * @param l the left parameter of the addition
   * @param r the right parameter of the addition
   * @return the newly created object
   */
  public static Term add(final Term l, final Term r) {
    return arith(l, r, NodeBuilder.funADD);
  }

  /**
   * Create an object representing an integer subtraction.
   * @param l the left parameter of the subtraction
   * @param r the right parameter of the subtraction
   * @return the newly created object
   */
  public static Term sub(final Term l, final Term r) {
    return arith(l, r, NodeBuilder.funSUB);

  }

  /**
   * Create an object representing an integer division.
   * @param l the left parameter of the division
   * @param r the right parameter of the division
   * @return the newly created object
   */
  public static Term div(final Term l, final Term r) {
    return arith(l, r, NodeBuilder.funDIV);
  }

  /**
   * Create an object representing an integer multiplication.
   * @param l the left parameter of the multiplication
   * @param r the right parameter of the multiplication
   * @return the newly created object
   */
  public static Term mul(final Term l, final Term r) {
    return arith(l, r, NodeBuilder.funMUL);
  }

  /**
   * Create an object representing an integer modulo.
   * @param l the left parameter of the modulo
   * @param r the right parameter of the modulo
   * @return the newly created object
   */
  public static Term mod(final Term l, final Term r) {
    return arith(l, r, NodeBuilder.funMOD);
  }

  /**
   * Build a term representing a left shift over 32 bits.
   * 
   * @param l the left side element of the shift
   * @param r the right side element of the shift
   * @return a well formed term of sort Int
   */
  public static Term lshift(final Term l, final Term r) {
    // 64 bits case is ignored at the moment 
    if (l.getSort() != r.getSort()) {
      throw new IllegalArgumentException("The sort of " + l + 
                                         " is different from the sort of " + r + ".");
    }
    FnTerm t = null;
    if (l.getSort() == Num.sortInt) {
      t = Formula.lf.mkFnTerm(Formula.lf.symIntFn, new Term[] {l, r});
      t.tag = NodeBuilder.funSL32;
    }
    else {
      throw new IllegalArgumentException("The sort " + l.getSort() + " is invalid!"); 
    }
    return t;
  }

  /**
   * Build a term representing a right shift over 32 bits.
   * 
   * @param l the left side element of the shift
   * @param r the right side element of the shift
   * @return a well formed term of sort Int
   */
  public static Term rshift(final Term l, final Term r) {
    // 64 bits case is ignored at the moment
    if (l.getSort() != r.getSort()) {
      throw new IllegalArgumentException("The sort of " + l + 
                                         " is different from the sort of " + r + ".");
    }
    FnTerm t = null;
    if (l.getSort() == Num.sortInt) {
      t = Formula.lf.mkFnTerm(Formula.lf.symIntFn, new Term[] {l, r});
      t.tag =  NodeBuilder.funASR32;
    }
    else {
      throw new IllegalArgumentException("The sort " + l.getSort() + " is invalid!"); 
    }
    return t;
  }

  /**
   * Build a term representing an unsigned right shift over 32 bits.
   * 
   * @param l the left side element of the shift
   * @param r the right side element of the shift
   * @return a well formed term of sort Int
   */
  public static Term urshift(final Term l, final Term r) {
    // 64 bits case is ignored at the moment
    if (l.getSort() != r.getSort() && 
        (!Num.isNum(r.getSort()) || !Num.isNum(l.getSort()))) {
      throw new IllegalArgumentException("The sort of " + l + 
                                         " is different from the sort of " + r + ".");
    }
    FnTerm t = null;
    if (l.getSort() == Num.sortInt) {
      t = Formula.lf.mkFnTerm(Formula.lf.symIntFn, new Term[] {l, r});
      t.tag = NodeBuilder.funUSR32;
    }
    else {
      throw new IllegalArgumentException("The sort " + l.getSort() + " is invalid!"); 
    }
    return t;
  }

  /**
   * Tell whether or not the given sort is a numerical sort.
   * @param sort a valid sort... not <code>null</code>
   * @return true if sort equals {@link #sortInt} or {@link #sortReal}
   */
  public static boolean isNum(final Sort sort) {
    return sort.equals(sortInt) || sort.equals(Heap.sortValue) || 
           sort.equals(sortReal);
  }

  /**
   * Build a formula that does the conversion from int to real.
   * @param r the term of sort integer to convert
   * @return a term of sort real
   */
  public static Term intToReal(final Term r) {
    return Formula.lf.mkFnTerm(Formula.lf.symIntToReal, new Term [] {r});
  }

  /**
   * Build a formula that represents a unary sub operation (it negates
   * the given term...).
   * @param t the term to add a minus sign around.
   * @return An Integer term or a real term
   */
  public static Term sub(final Term t) {
    if (t.getSort().equals(sortInt)) {
      return Formula.lf.mkFnTerm(Formula.lf.symIntegralNeg, new Term [] {t});
    }
    else if (t.getSort().equals(sortReal)) {
      return Formula.lf.mkFnTerm(Formula.lf.symFloatingNeg, new Term [] {t});

    }
    else {
      throw new IllegalArgumentException("The sort " + t.getSort() + " is invalid!"); 
    }

  }

  /**
   * Build a formula that represents a bit not operation.
   * @param t the term to do a bitnot with around.
   * @return An Integer term or a real term
   */
  public static Term bitnot(final Term t) {
    if (t.getSort().equals(sortInt)) {
      final FnTerm f = Formula.lf.mkFnTerm(Formula.lf.symIntFn, new Term [] {t});
      f.tag = NodeBuilder.funNEG;
      return f;

    }
    else if (t.getSort().equals(sortReal)) {
      final FnTerm f = Formula.lf.mkFnTerm(Formula.lf.symRealFn, new Term [] {t});
      f.tag = NodeBuilder.funNEG;
      return f;
    }
    else {
      throw new IllegalArgumentException("The sort " + t.getSort() + " is invalid!"); 
    }

  }
  /**
   * Build a formula that represents the increment of 1 of the given term.
   * @param t the term to increment
   * @return a formula that represents the incrementation of the given term
   */
  public static Term inc(final Term t) {
    return Num.add(t, Num.value(1));
  }
  
  /**
   * Build a formula that represents the decrement of 1 of the given term.
   * @param t the term to decrement
   * @return a formula that represents the decrementation of the given term
   */
  public static Term dec(final Term t) {
    return Num.sub(t, Num.value(1));
  }
}
