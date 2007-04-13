/**
 * 
 */
package mobius.directVCGen.vcgen.struct;

import javafe.ast.Type;

public class ExcpPost {
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