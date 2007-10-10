package mobius.directVCGen.formula;

import java.util.HashMap;
import java.util.List;
import java.util.Map;

import javafe.ast.RoutineDecl;
import javafe.ast.TypeDecl;
import mobius.directVCGen.vcgen.struct.Post;
import escjava.sortedProver.Lifter.Term;

/**
 * @author hel
 *
 */
public class Lookup {
  
  /** Defines whether 'null' can be returned or not. 
   *  If fFailSave is true, a default Term is returned
   *  instead of 'null' */
  public static final boolean fFailSave = false;
  
  /** an instance of the lookup object. */
  private static final Lookup inst = new Lookup();
  
  
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
  
  /** the argument lists of each precondition. */
  private final Map<RoutineDecl, List<Term>> fPreArgs = 
    new HashMap<RoutineDecl, List<Term>>(); 
  
  
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
  
  /**
   * Returns the current instance of the lookup object.
   * @return cannot be null
   */
  public static Lookup getInst() {
    return inst;
  }

  public List<Term> addPreconditionArgs(final RoutineDecl m,
                                        final List<Term> args) {
    if (args == null) {
      throw new NullPointerException("" + m);
    }
    return fPreArgs.put(m, args);
  }
  public List<Term> getPreconditionArgs(final RoutineDecl m) {
    return fPreArgs.get(m);
  }
  
  /**
   * @return the content of the object
   */
  @Override
  public String toString() {
    final String pre = "Preconditions: \n" +
                       "Arguments:" + fPreArgs + "\n" +
                       "Terms: " + preconditions + "\n";
    return pre;
           
  }
}
