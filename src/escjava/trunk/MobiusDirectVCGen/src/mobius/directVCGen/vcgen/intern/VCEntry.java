package mobius.directVCGen.vcgen.intern;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;

import mobius.directVCGen.formula.Logic;

import javafe.ast.Identifier;
import javafe.ast.Type;
import javafe.ast.TypeDecl;
import escjava.sortedProver.Lifter.QuantVariableRef;
import escjava.sortedProver.Lifter.Term;

public class VCEntry {
	
	public Post post;
	
	/** the excp post condition... */
	public final List<ExcpPost> lexcpost = new ArrayList<ExcpPost>();
	public final Post excpost; 
	public final HashMap<Identifier, Post> lbrpost = new HashMap<Identifier, Post>(); 
	public Post brpost;
	public final HashMap<Identifier, Post> lcontpost = new HashMap<Identifier, Post>(); 
	public Post contpost;

	public VCEntry (Post exc) {
        excpost = exc;    		
	}
	
	public VCEntry () {
        excpost = null;    		
	}
		
	public VCEntry(VCEntry ve) {
		post = ve.post;
		brpost = ve.brpost;
		contpost = ve.contpost;
		excpost = ve.excpost;
		lexcpost.addAll(ve.lexcpost);
		lbrpost.putAll(ve.lbrpost);
		lcontpost.putAll(ve.lcontpost);
	}

	public static class ExcpPost {
		public final Type excp;
		public final Post post;
		public ExcpPost (Type excp, Post p) {
			this.excp = excp;
			this.post = p;
		}
		public String toString() {
			return "( " + excp + ", " + post + ")";
		}
	
	}

	public static class Post {
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
				return "temp var:" + var  + "\npostcondition : " + post;
			}
			return  "\npostcondition : " + post;
		}
	}
}