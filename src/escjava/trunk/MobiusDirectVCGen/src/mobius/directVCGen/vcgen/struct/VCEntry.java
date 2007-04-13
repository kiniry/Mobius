package mobius.directVCGen.vcgen.struct;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;

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
        excpost = exc;    		
	}
	
	public VCEntry () {
        excpost = null;    		
	}
	public VCEntry(Post post, Post excpost, Post brpost, Post contpost) {
		this.post = post;
		this.brpost = brpost;
		this.contpost = contpost;
		this.excpost = excpost;
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