package mobius.directVCGen.formula;

import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.Vector;

import mobius.directVCGen.vcgen.struct.Post;

import escjava.ast.Modifiers;
import escjava.ast.TagConstants;
import escjava.sortedProver.Lifter.QuantVariable;
import escjava.sortedProver.Lifter.Term;
import escjava.sortedProver.NodeBuilder.FnSymbol;
import escjava.sortedProver.NodeBuilder.Sort;
import javafe.ast.ClassDecl;
import javafe.ast.ConstructorDecl;
import javafe.ast.FormalParaDecl;
import javafe.ast.FormalParaDeclVec;
import javafe.ast.MethodDecl;
import javafe.ast.RoutineDecl;

/**
 * @author hel
 *
 */
public class Lookup {
  
  /** list of symbols to declare. */
  public static List<FnSymbol> symToDeclare = new Vector<FnSymbol>();

  /** the list of fields to declare. */
  public static Set<QuantVariable> fieldsToDeclare = new HashSet<QuantVariable>();

  /** map containing RoutineDecl as keys and Terms (the precondition) as value. **/
  public static Map<RoutineDecl, Term> preconditions = new HashMap<RoutineDecl, Term>();

  /** map containing RoutineDecl as keys and Terms (the postcondition) as value. **/
  public static Map<RoutineDecl, Post> postconditions = new HashMap<RoutineDecl, Post>();

  /** map containing RoutineDecl as keys and Terms (the exceptional postcondition) as value. */
  public static Map<RoutineDecl, Post> exceptionalPostconditions = 
    new HashMap<RoutineDecl, Post>();

  /** map containing ClassDecl as keys and Terms (the invariant) as value. **/
  public static Map<ClassDecl, Term> invariants = new HashMap<ClassDecl, Term>();


  /**
   * Build a condition which is made of a custom predicate with the method's argument 
   * applied to it.
   * It's used for testing purpose only.
   * @param m the method to get a predicate out of
   * @param name the name of the method
   * @param hasResult whether or not it has a result
   * @return a term built around the rules stated above
   */
  public static Term buildStdCond (final RoutineDecl m, String name, boolean hasResult) {
    int arity = m.args.size();
    boolean incThis = false;

    //Sort returnType = Ref.sort;  
    if (m instanceof MethodDecl) {
      //returnType = Type.getReturnType((MethodDecl) m);
      if ((m.getModifiers() & Modifiers.ACC_STATIC) == 0) {
        arity++;
        incThis = true;
      }
    }

    if ((m instanceof ConstructorDecl)
        || ((MethodDecl) m).returnType.getTag() == TagConstants.VOIDTYPE) {
      hasResult = false;
    }
    if (hasResult) {
      arity++;
    }
    final Sort [] s = new Sort[arity];
    final Term [] args = new Term [arity];
    if (incThis) {
      s [0] = Ref.sort;
      args[0] = Ref.varThis;
    }
    final FormalParaDeclVec v = m.args;
    for (int i = 0; i < v.size(); i++) {
      final FormalParaDecl para = v.elementAt(i);
      args[i + 1] = Expression.rvar(para);
      s[i + 1] = args[i + 1].getSort();

    }
    if (hasResult) {
      //m instance of MethodDecl
      final MethodDecl dec = (MethodDecl) m;
      args[args.length - 1] = Expression.rvar(Expression.getResultVar(dec));
      s[s.length - 1] = args[args.length - 1].getSort();
    }
    if (m instanceof ConstructorDecl) {
      name = ((ConstructorDecl) m).parent.id + name;
    }
    else {
      name = ((MethodDecl) m).id + name;
    }
    final FnSymbol sym = Formula.lf.registerPredSymbol(name, s);
    symToDeclare.add(sym);

    return Formula.lf.mkFnTerm(sym, args);

  }
  /**
   * Returns the FOL Term representation of the precondition of method m.
   * @param m the method of interest
   */
  public static Term precondition(final RoutineDecl m) {
    //return buildStdCond(m, "_pre", false);
    return preconditions.get(m);
  }

  /**
   * Returns the FOL Term representation of the normal postcondition of routine m.
   * @param m the method of interest
   */
  public static Post normalPostcondition(final RoutineDecl m) {
    //return new Post(buildStdCond (m, "_norm", true)); 
    return postconditions.get(m);
  }

  /**
   * Returns the FOL Term representation of the normal postcondition of method m.
   * @param m the method of interest
   */
  public static Post normalPostcondition(final MethodDecl m) {
    //return new Post(Expression.rvar(Expression.getResultVar(m)), 
    //                buildStdCond (m, "_norm", true)); 
    return postconditions.get(m);
  }
  /**
   * Returns a vector of FOL Term representations of the exceptional 
   * postconditions of method m.
   * The exceptional postcondition will always look like this: Sort => Term
   * @param m the method of interest
   */
  public static Post exceptionalPostcondition(final RoutineDecl m) {
    //return new Post(Expression.rvar(Ref.sort), buildStdCond (m, "_excp", false)); 
    return exceptionalPostconditions.get(m);
  }

}
