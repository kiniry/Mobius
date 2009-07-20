/*
 * Created on Apr 20, 2005
 *
 * To change the template for this generated file go to
 * Window&gt;Preferences&gt;Java&gt;Code Generation&gt;Code and Comments
 */
package jml2b.structure;

import jml2b.structure.java.Declaration;
import jml2b.structure.java.Modifiers;
import jml2b.structure.java.ParsedItem;
import jml2b.structure.java.Type;
import jml2b.structure.statement.Expression;
import jml2b.link.Linkable;

/**
 *
 *  @author L. Burdy
 **/
public abstract class AField extends Declaration implements Linkable {

	public AField() {}
	
	 public AField(ParsedItem pi, Modifiers mods) {
        super(pi, mods);
}
	 
	 public abstract Type getType();
	 
	 public abstract boolean isExpanded();
	 
	 public abstract boolean isLocal();
	 
	 public abstract Expression getAssign();
	 
	 
}
