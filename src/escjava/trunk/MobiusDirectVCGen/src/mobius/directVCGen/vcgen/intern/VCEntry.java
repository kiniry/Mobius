package mobius.directVCGen.vcgen.intern;

import java.util.HashMap;

import javafe.ast.Identifier;
import javafe.ast.TypeDecl;
import escjava.sortedProver.Lifter.QuantVariableRef;
import escjava.sortedProver.Lifter.Term;

public class VCEntry {
	
	public Post post;
	
	/** the excp post condition... */
	public final HashMap<TypeDecl, Post> excpost = new HashMap<TypeDecl, Post>();
	
	public final HashMap<Identifier, Post> lbrpost = new HashMap<Identifier, Post>(); 
	public Post brpost;
	public final HashMap<Identifier, Post> lcontpost = new HashMap<Identifier, Post>(); 
	public Post contpost;
	
	public VCEntry () {
		
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
		
		public String toString() {
			if(var != null) {
				return "temp var:" + var  + "\npostcondition : " + post;
			}
			return  "\npostcondition : " + post;
		}
	}
}