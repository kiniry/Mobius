package mobius.directVCGen.formula;

import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.Vector;

import javafe.ast.ConstructorDecl;
import javafe.ast.FormalParaDecl;
import javafe.ast.FormalParaDeclVec;
import javafe.ast.MethodDecl;
import javafe.ast.RoutineDecl;
import javafe.ast.TypeDecl;
import mobius.directVCGen.vcgen.struct.Post;
import escjava.ast.Modifiers;
import escjava.ast.TagConstants;
import escjava.sortedProver.Lifter.QuantVariable;
import escjava.sortedProver.Lifter.Term;
import escjava.sortedProver.NodeBuilder.FnSymbol;
import escjava.sortedProver.NodeBuilder.Sort;

/**
 * @author hel
 *
 */
public class Lookup {
  
  /** Defines whether 'null' can be returned or not. 
   *  If fFailSave is true, a default Term is returned
   *  instead of 'null' */
  public final static boolean fFailSave=false;
  
  /** list of symbols to declare. */
  public static List<FnSymbol> symToDeclare = new Vector<FnSymbol>();

  /** the list of fields to declare. */
  public static Set<QuantVariable> fieldsToDeclare = new HashSet<QuantVariable>();

  /** map containing RoutineDecl as keys and Terms (the precondition) as value. **/
  public static Map<RoutineDecl, Term> preconditions = new HashMap<RoutineDecl, Term>();

  /** map containing RoutineDecl as keys and Terms (the postcondition) as value. **/
  public static Map<RoutineDecl, Post> postconditions = new HashMap<RoutineDecl, Post>();

  /** map containing RoutineDecl as keys and Terms (the exceptional postcondition) as value. */
  private static Map<RoutineDecl, Post> exceptionalPostconditions = 
    new HashMap<RoutineDecl, Post>();

  /** map containing ClassDecl as keys and Terms (the invariant) as value. **/
  public static Map<TypeDecl, Term> invariants = new HashMap<TypeDecl, Term>();

  /** map containing ClassDecl as keys and Terms (the constraint) as value. **/
  public static Map<TypeDecl, Term> constraints = new HashMap<TypeDecl, Term>();

  /**
   * Build a condition which is made of a custom predicate with the method's argument 
   * applied to it.
   * It's used for testing purpose only.
   * @param m the method to get a predicate out of
   * @param name the name of the method
   * @param hasResult whether or not it has a result
   * @return a term built around the rules stated above
   * @deprecated
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
   * @return the precondition or <code>True</code>
   */
  public static Term precondition(final RoutineDecl m) {
    //return buildStdCond(m, "_pre", false);
    Term t = preconditions.get(m);
    if (t == null) {
      t = Logic.True();
    }
    return t;
  }

  /**
   * Returns the FOL Term representation of the normal postcondition of routine m.
   * @param m the method of interest
   * @return the normal postcondition or <code>True</code>
   */
  public static Post normalPostcondition(final RoutineDecl m) {
    //return new Post(buildStdCond (m, "_norm", true)); 
    Post p = postconditions.get(m);
    if (p == null) {
      p = new Post(Logic.True());
    }
    return p;
  }

//  /**
//   * Returns the FOL Term representation of the normal postcondition of method m.
//   * @param m the method of interest
//   */
//  public static Post normalPostcondition(final MethodDecl m) {
//    //return new Post(Expression.rvar(Expression.getResultVar(m)), 
//    //                buildStdCond (m, "_norm", true)); 
//    return postconditions.get(m);
//  }
  /**
   * Returns a vector of FOL Term representations of the exceptional 
   * postconditions of method m.
   * The exceptional postcondition will always look like this: Sort => Term
   * @param m the method of interest
   * @return the exceptional postcondition or <code>True</code>
   */
  public static Post getExceptionalPostcondition(final RoutineDecl m) {
    //return new Post(Expression.rvar(Ref.sort), buildStdCond (m, "_excp", false)); 
    Post p = exceptionalPostconditions.get(m);
    if (p == null) {
      p = new Post(Expression.rvar(Ref.sort), Logic.True());
    }
    return p;
  }

  /**
   * Adds a given Term to exceptional postconditions of a given method. 
   * @param rd the method
   * @param post to add to exceptional postconditions in Lookup hash map
   */
  public static void addExceptionalPostcondition(final RoutineDecl rd, 
                                                 final Post post) {
    Post pNew = post;
    
    if (pNew == null) {
      pNew = new Post(Expression.rvar(Ref.sort), Logic.True());
    }
    if (pNew.getRVar() == null) {
      // we have to fix that
      pNew = new Post(Expression.rvar(Ref.sort), pNew);
    }
    
    final Post pOld = exceptionalPostconditions.get(rd);
    if (pOld != null) {
      // not the first time
      pNew = Post.and(pNew, pOld);
    }
    exceptionalPostconditions.put(rd, pNew);
  }


  public static void addExceptionalPostcondition(RoutineDecl rd, Term term) {
    final Post pOld = exceptionalPostconditions.get(rd);
    Post pNew;
    if (pOld == null) {
      pNew = new Post(Expression.rvar(Ref.sort), term);
    }
    else {
      pNew = Post.and(pOld, term);
    }
    exceptionalPostconditions.put(rd, pNew);
  }

}
