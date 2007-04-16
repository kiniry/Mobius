package mobius.directVCGen.vcgen.struct;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;

import mobius.directVCGen.formula.Expression;
import mobius.directVCGen.formula.Logic;
import mobius.directVCGen.formula.Ref;

import javafe.ast.Identifier;

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
		this(null, exc, null, null);
	}
	
	public VCEntry () {
		this(null, null, null, null);
	}
	public VCEntry(Post post, Post excpost, Post brpost, Post contpost) {
		this.post = post;
		this.brpost = brpost;
		this.contpost = contpost;
		this.excpost =  new Post(Expression.refFromVar(Expression.var("e", Ref.sort)),
								 Expression.refFromVar(Expression.var("excp post", Logic.sort))); //excpost;
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
}