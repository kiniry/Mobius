
package mobius.directVCGen.vcgen.struct;

import mobius.directVCGen.formula.Logic;
import escjava.sortedProver.Lifter.QuantVariable;
import escjava.sortedProver.Lifter.QuantVariableRef;
import escjava.sortedProver.Lifter.Term;

/**
 * The data structure representing a postcondition.
 * It is a variable associated with a logic formula.
 * @author J. Charles and B. Grégoire (julien.charles, benjamin.gregoire)@inria.fr
 */
public class Post {
  /** the temporary variable; used mainly in the vcGen of expressions. */
  private final QuantVariableRef fVar;

  /** the current postcondition. */
  private final Term fPost;

  /**
   * Construct a postcondition from a variable and a logical formula.
   * @param var the current substitution variable
   * @param post the logical formula
   */
  public Post (final QuantVariableRef var, final Term post) {
    fVar = var;
    fPost = post;
  }

  /**
   * Construct a postcondition from a logical formula.
   * No variable is associated with it.
   * @param post the logical formula
   */
  public Post (final Term post) {
    this(null, post);
  }

  /**
   * Construct a postcondition from a variable and a postcondition.
   * @param var the variable to be replaced
   * @param post the predicate being postcondition
   */
  public Post(final QuantVariableRef var, final Post post) {
    this(var, post.fPost);
  }

  /**
   * Substitute the current variable ({@link #fVar}) with the logical formula given
   * as an argument.
   * @param f the formula to substitute the variable with
   * @return a term where the variable has been substituted
   */
  public Term substWith(final Term f) {
    if (fVar != null) {
      return fPost.subst(fVar, f);
    }
    return fPost;
  }
  
  /**
   * Substitute the current variable ({@link #fVar}) with the logical formula given
   * as an argument.
   * @param v a variable or an expression to substitute
   * @param f the formula to substitute the variable with
   * @return a term where the variable has been substituted
   */
  public Term subst(final Term v, final Term f) {
    if ((v != null) && (f != null)) {
      return fPost.subst(v, f);
    }
    return fPost;
  }

  /**
   * Make one post out of two (isn't that magickal?) and does it robustly.
   * If one of the argument is <code>null</code> it simply returns the other.
   * In the case if both are different from <code>null</code> it joins
   * them with an end and replaces the variable of the second by the one of the
   * first. The result is of this form 
   * <code>{p1.var, (p1.post /\ p2.post[p2.var \ p1.var])}</code>.
   * The and used is the one presented in the 
   * {@link mobius.directVCGen.formula.Logic#and(Term, Term)} method.
   * @param p1 the left part of the <code>and</code>
   * @param p2 the right part of the <code>and</code>
   * @return a new Post object with the properties mentionned above or p1 or p2
   */
  public static Post and(final Post p1, final Post p2) {
    if (p1 == null) return p2;
    if (p2 == null) return p1;
    return new Post(p1.fVar, 
                    Logic.and(p1.fPost, p2.subst(p2.fVar, p1.fVar)));
  }

  /**
   * Nearly the same semantic as the {@link #and(Post, Post)} method.
   * The only difference is that it builds an implies.
   * @param p1 the left part of the <code>implies</code>
   * @param p2 the right part of the <code>implies</code>
   * @return a new Post object with the properties mentionned above or p1 or p2
   */
  public static Post implies(final Post p1, final Post p2) {
    if (p1 == null) return p2;
    if (p2 == null) return p1;
    return new Post(p1.fVar, 
                    Logic.implies(p1.fPost, p2.subst(p2.fVar, p1.fVar)));
  }
  /**
   * Nearly the same semantic as the {@link #implies(Post, Post)} method.
   * @param p1 the left part of the <code>implies</code>
   * @param p2 the right part of the <code>implies</code>
   * @return a Term object with the properties mentionned above or p1 or p2
   */
  public static Term implies(final Term p1, final Post p2) {
    if (p1 == null) return p2.fPost;
    if (p2 == null) return p1;
    return Logic.implies(p1, p2.fPost);
  }
  
  /**
   * Adds a not to the post inside the argument. It returns a post of the
   * form <code>{p1.var, not(p1.post)}</code>. It uses the method
   * {@link Logic#not(Term, Term)} to do the job.
   * @param p1 the term to negate
   * @return a new post
   */
  public static Post not(final Post p1) {
    if (p1 == null || p1.fPost == null) {
      throw new IllegalArgumentException("" + p1);
    }
    return new Post(p1.fVar, 
                    Logic.not(p1.fPost));
  }


  /**
   * @return a string of the form
   * <code>(var: var) (post: post)</code> or
   * <code>(post: post)</code> if var is missing
   */
  public String toString() {
    if (fVar != null) {
      return "(var:" + fVar  + ") (post: " + fPost + ")";
    }
    return  "(post: " + fPost + ")";
  }
  
  /**
   * @return the current postcondition
   * @deprecated use {@link #implies(Post, Post)}, {@link #and(Post, Post)}
   * or {@link #not(Post)} instead
   */
  public Term getPost() {
    return fPost;
  }
  
  /**
   * @return the parameter variable
   */
  public QuantVariableRef getRVar() {
    return fVar;
  }
  /**
   * @return the parameter variable
   */
  public QuantVariable getVar() {
    return fVar.qvar;
  }
}
