package escjava.vcGeneration;

abstract class TLiteral extends TVariable {

    public /*@ non_null @*/ StringBuffer toDot(){

	/* dot id which is unique because of adding 
	   'id' to the name of the node */
	StringBuffer r = new StringBuffer(dotId());

	/* add fancy stuff, like square box o_O */

	/*
	 * Contrary to all other nodes, here we did not display
	 * the name of the class as label, but the type.
	 */
	r.append(" [shape=box, label=\"\\["+getType());

	return r; /* it's the job of the caller to finish */
    }

}
