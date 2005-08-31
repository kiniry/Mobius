package escjava.vcGeneration;

import java.lang.Class;
import java.io.PrintStream;
import java.util.Vector;
import java.util.Iterator;
import java.lang.StringBuffer;

abstract class TVariable extends TNode {

    public /*@ non_null @*/ StringBuffer toDot(){

	/* dot id which is unique because of adding 
	   'id' to the name of the node */
	StringBuffer r = new StringBuffer(dotId());

	/* add fancy stuff, like square box o_O */
	r.append(" [shape=box, label="+getShortName());

	// write the type (if exists)
	if(type!=null){
	    /* the old type is contained into the 'type' field which has
	       type 'typeInfo' ouf! */

	    r.append("\\n\\["+getType()+"\\]"); 
	}

	r.append("\"];\n");
	
	return r;
    }

    /*
     * This method does nothing and is not abstract
     * because some of the subclasses did not need to
     * do something when this method is called.
     */
    protected void typeTree(){};

}
