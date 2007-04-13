/**
 * 
 */
package mobius.directVCGen.vcgen.struct;

import mobius.directVCGen.formula.Logic;
import escjava.sortedProver.Lifter.QuantVariableRef;
import escjava.sortedProver.Lifter.Term;

public class Post {
	/** the temporary variable; used in the vcGen of expressions */
	public final QuantVariableRef var;
	
	/** the current postcondition */
	public final Term post;	
	
	public Post (QuantVariableRef var, Term post) {
		this.var = var;
		this.post = post;
	}
	
	public Post (Term post) {
		this(null, post);
	}
	
	public Term substWith(Term f) {
		if(var != null) {
			return post.subst(var, f);
		}
		return post;
	}
	public static Post and(Post p1, Post p2) {
		if (p1 == null) return p2;
		if (p2 == null) return p1;
		return new Post(p1.var, 
				Logic.and(p1.post, p2.post.subst(p2.var, p1.var)));
	}
	public static Post implies(Post p1, Post p2) {
		if (p1 == null) return p2;
		if (p2 == null) return p1;
		return new Post(p1.var, 
				Logic.implies(p1.post, p2.post.subst(p2.var, p1.var)));			
	}
	public static Post not(Post p1) {
		return new Post(p1.var, 
				Logic.not(p1.post));			
	}
	public String toString() {
		if(var != null) {
			return "(var:" + var  + ") (postcondition : " + post + ")";
		}
		return  "(postcondition : " + post + ")";
	}
}