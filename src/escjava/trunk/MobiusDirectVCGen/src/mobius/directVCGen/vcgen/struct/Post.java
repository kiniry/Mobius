
package mobius.directVCGen.vcgen.struct;

import mobius.directVCGen.formula.Logic;
import escjava.sortedProver.Lifter.QuantVariableRef;
import escjava.sortedProver.Lifter.Term;

/**
 * The data structure representing a postcondition. 
 * It is a variable associated with a logic formula.
 * @author J. Charles and B. Grégoire
 */
public class Post {
	/** the temporary variable; used mainly in the vcGen of expressions */
	public final QuantVariableRef var;
	
	/** the current postcondition */
	public final Term post;	
	
	/**
	 * Construct a postcondition from a variable and a logical formula.
	 * @param var the current substitution variable
	 * @param post the logical formula
	 */
	public Post (QuantVariableRef var, Term post) {
		this.var = var;
		this.post = post;
	}
	
	/**
	 * Construct a postcondition from a logical formula.
	 * No variable is associated with it.
	 * @param post the logical formula
	 */
	public Post (Term post) {
		this(null, post);
	}
	
	/**
	 * Substitute the current variable ({@link #var}) with the logical formula given
	 * as an argument.
	 * @param f the formula to substitute the variable with
	 * @return a term where the variable has been substituted
	 */
	public Term substWith(Term f) {
		if(var != null) {
			return post.subst(var, f);
		}
		return post;
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
	public static Post and(Post p1, Post p2) {
		if (p1 == null) return p2;
		if (p2 == null) return p1;
		return new Post(p1.var, 
				Logic.and(p1.post, p2.post.subst(p2.var, p1.var)));
	}
	
	/**
	 * Nearly the same semantic as the {@link #and(Post, Post)} method.
	 * The only difference is that it builds an implies.
	 */
	public static Post implies(Post p1, Post p2) {
		if (p1 == null) return p2;
		if (p2 == null) return p1;
		return new Post(p1.var, 
				Logic.implies(p1.post, p2.post.subst(p2.var, p1.var)));			
	}
	
	/**
	 * Adds a not to the post inside the argument. It returns a post of the
	 * form <code>{p1.var, not(p1.post)}</code>. It uses the method
	 * {@link Logic#not(Term, Term)} to do the job.
	 * @param p1 the term to negate
	 * @return a new post
	 */
	public static Post not(Post p1) {
		if(p1 == null || p1.post == null) {
			throw new NullPointerException("" + p1);
		}
		return new Post(p1.var, 
				Logic.not(p1.post));			
	}
	
	/*
	 * (non-Javadoc)
	 * @see java.lang.Object#toString()
	 */
	public String toString() {
		if(var != null) {
			return "(var:" + var  + ") (post: " + post + ")";
		}
		return  "(post: " + post + ")";
	}
}