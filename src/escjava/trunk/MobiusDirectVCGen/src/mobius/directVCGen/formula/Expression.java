package mobius.directVCGen.formula;

import javafe.ast.GenericVarDecl;
import javafe.ast.MethodDecl;
import escjava.ast.TagConstants;
import escjava.sortedProver.Lifter.FnTerm;
import escjava.sortedProver.Lifter.QuantVariable;
import escjava.sortedProver.Lifter.QuantVariableRef;
import escjava.sortedProver.Lifter.Term;
import escjava.sortedProver.NodeBuilder.Sort;
import escjava.translate.UniqName;

/**
 * The library file used to represent expressions.
 * The main functions in this libraries are the one to 
 * handle variables, reference on variables, and old versions
 * of variables.
 * @author J. Charles (julien.charles@inria.fr), H. Lehner
 */
public final class Expression {

  /** the prefix used to mark variables as old (<code>\pre_</code>). */
  public static final String oldPrefix = "\\pre_";

  /** the special field which represents the length of an array. */
  public static final QuantVariable length;
  
  /** counter to create anonymous variables. */
  private static final int [] varCounters = {0, 0, 0, 0, 0};

  /** the name of the result variable (<code>\result</code>). */
  private static final String result = "\\result";

  

  static {
    length = var("length", Num.sortInt);
    Lookup.fieldsToDeclare.add(length);
  }
  
  /**
   * @deprecated
   */
  private Expression() {
  }

  /**
   * This method is used to <i>make old</i> the given name.
   * It should not be used outside this library as it is a helper
   * method for all the other old methods:
   * <ul>
   * <li> {@link #old(GenericVarDecl)}, </li>
   * <li> {@link #old(QuantVariable)} and </li>
   * <li> {@link #old(QuantVariableRef)} </li>
   * </ul>
   * @param name the name to make old
   * @return the oldified name
   */
  private static String old(final String name) {
    return oldPrefix + name;
  }

  /**
   * Creates an old version of the given variable.
   * @param decl The variable to convert to an old version
   * of it.
   * @return the <i>oldified</i> version of the variable
   */
  public static QuantVariableRef old(final GenericVarDecl decl) {
    return rvar(Formula.lf.mkQuantVariable(decl, old(UniqName.variable(decl))));
  }

  /**
   * Turn a quant variable to an old quant variable.
   * @param qv The quant variable to make old. 
   * @return The <i>oldified</i> version of the variable
   */
  public static QuantVariable old(final QuantVariable qv) {
    return var(old(qv.name), qv.type);
  }

  /**
   * Turn a quant variable ref to an old quant variable.
   * @param qvr The quant variable ref to make old. 
   * @return The <i>oldified</i> version of the variable

   */
  public static QuantVariableRef old(final QuantVariableRef qvr) {
    return rvar(old(qvr.qvar));
  }


  /**
   * Build a variable from a string, without any specified sort.
   * It is here for development/testing purpose only, therefore
   * it is marked as deprecated.
   * @param str the name of the variable
   * @return a variable of the sort any ({@link Formula#sort})
   * @deprecated use another method instead, like {@link #var(Sort)}
   */
  public static QuantVariable var(final String str) {
    return var(str, Formula.sort);
  }

  /**
   * Creates a quantified variable from its name and its type.
   * @param name a name for the variable
   * @param s the sort of the variable
   * @return a variable with the given name and sort
   */
  public static QuantVariable var(final String name, final Sort s) {
    return Formula.lf.mkQuantVariable(name, s);
  }

  /**
   * Creates a variable from a generic variable declaration definition.
   * @param decl the declaration to turn into a quantified variable
   * @return a quant variable corresponding to the given declaration
   */
  public static QuantVariable var(final GenericVarDecl decl) {
    return Formula.lf.mkQuantVariable(decl, UniqName.variable(decl));
  }

  /**
   * Create an anonymous variable of given type.
   * @param s the sort of the variable
   * @return a newly created variable with a name that will not interfere
   * with any other. It is <b>Unique</b>!
   */
  public static QuantVariable var(final Sort s) {
    String name = "#";
    if (s == Bool.sort) {
      name += "b" + varCounters[0];
      varCounters[0]++;
    } 
    else if (s == Ref.sort) {
      name += "r" + varCounters[1];
      varCounters[1]++;
    }
    else if (s == Num.sortInt) {
      name += "i" + varCounters[2];
      varCounters[2]++;
    }
    else if (s == Num.sortReal) {
      name += "f" + varCounters[3];
      varCounters[3]++;
    }
    else {
      name += "x" + varCounters[4];
      varCounters[4]++;
    }
    return Formula.lf.mkQuantVariable(name, s);
  }

  /**
   * Create an anonymous variable, as a QuantVarRef.
   * It is based on the method {@link #var(Sort)}.
   * @param s the sort the variable will be of
   * @return a newly created variable, whose name should
   * not collide with already existing ones
   */
  public static QuantVariableRef rvar(final Sort s) {
    return rvar(var(s));
  }

  /**
   * Returns the reference over a variable corresponding
   * to the given variable declaration.
   * @see #var(GenericVarDecl)
   * @param arg the variable to translate
   * @return a variable reference corresponding to the declaration
   */
  public static QuantVariableRef rvar(final GenericVarDecl arg) {
    return rvar(var(arg));
  }

  /**
   * Returns a reference over a variable which has the given
   * name and sort.
   * @see #var(String, Sort)
   * @param name the name of the variable
   * @param s the sort of the variable
   * @return a reference over a variable
   */
  public static QuantVariableRef rvar(final String name, final Sort s) {
    return rvar(var(name, s));
  }


  /**
   * Returns the reference corresponding to the given variable.
   * @param qv the quant variable to get a reference from
   * @return a reference over the given variable
   */
  public static QuantVariableRef rvar(final QuantVariable qv) {
    return Formula.lf.mkQuantVariableRef(qv);
  }

  /**
   * The method to build a term which has its return type 
   * the same as its argument. 
   * @see #bitand(Term, Term)
   * @see #bitor(Term, Term)
   * @see #bitxor(Term, Term)
   * 
   * @param l the left side argument
   * @param r the right side argument
   * @param tag the tag which gives its meaning to the node 
   * @return a newly built term
   */
  private static Term binaryOp(final Term l, final Term r, final int tag) {
    if (l.getSort() != r.getSort())
      throw new IllegalArgumentException("The sort of " + l + 
                                         " is different from the sort of " + r + ".");
    FnTerm t = null;
    if (l.getSort() == Bool.sort) {
      t = Formula.lf.mkFnTerm(Formula.lf.symBoolFn, new Term[] {l, r});
    }
    else if (l.getSort() == Num.sortInt) {
      t = Formula.lf.mkFnTerm(Formula.lf.symIntFn, new Term[] {l, r});
    }
    else if (l.getSort() == Num.sortReal) {
      t = Formula.lf.mkFnTerm(Formula.lf.symRealFn, new Term[] {l, r});
    }
    else {
      throw new IllegalArgumentException("The sort " + l.getSort() + " is invalid!"); 
    }
    t.tag = tag;
    return t;
  }

  /**
   * Represents a bitwise or. It can be of type bool,
   * integer or real.
   * @param l the left side of the operand
   * @param r the right side
   * @return a term representing a bitwise or
   */
  public static Term bitor(final Term l, final Term r) {
    return binaryOp(l, r, TagConstants.BITOR);
  }

  /**
   * Represents a bitwise xor. It can be of type bool,
   * integer or real.
   * @param l the left side of the operand
   * @param r the right side
   * @return a term representing a bitwise xor
   */
  public static Term bitxor(final Term l, final Term r) {
    return binaryOp(l, r, TagConstants.BITXOR);
  }

  /**
   * Represents a bitwise and. It can be of type bool,
   * integer or real.
   * @param l the left side of the operand
   * @param r the right side
   * @return a term representing a bitwise and
   */
  public static Term bitand(final Term l, final Term r) {
    return binaryOp(l, r, TagConstants.BITAND);
  }


  /**
   * Create a symbol. There should be no symbols without a meaning
   * attached to it. Therefore it is deprecated and there is no
   * replacement to it.
   * @param name the name of the symbol
   * @param s the sort of the symbol
   * @return a symbol of the specified sort
   * @deprecated
   */
  public static FnTerm sym(final String name, final Sort s) {
    return Formula.lf.symbolRef (name, s);
  }

  /**
   * Return a variable representing a result, with its type
   * corresponding to the return type of the given method.
   * @param meth the methode to which the result belong
   * @return a variable representing the result of the method
   */
  public static QuantVariable getResultVar(final MethodDecl meth) {
    return var(Expression.result, Type.getReturnType(meth));
  }

  /**
   * Return a reference to a variable representing a result, 
   * with its type corresponding to the return type of the 
   * given method.
   * @param meth the methode to which the result belong
   * @return a variable ref representing the result of the method
   */
  public static QuantVariableRef getResultRVar(final MethodDecl meth) {
    return rvar(Expression.result, Type.getReturnType(meth));
  }

}
