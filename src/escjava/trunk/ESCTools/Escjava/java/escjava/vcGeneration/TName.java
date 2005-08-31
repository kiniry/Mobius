package escjava.vcGeneration;

class TName extends TVariable {

    /*@ non_null @*/ String name;

    /*
     * type is supposed to be one of the object that is statically
     * initialized in TNode, like $Reference, $Type etc...
     */
    protected TName(/*@ non_null @*/ String name){
	this.name = name;
    }

  public /*@ non_null @*/ StringBuffer toDot(){

    /* dot id which is unique because of adding 
     'id' to the name of the node */
    StringBuffer r = new StringBuffer(dotId());

    /* add fancy stuff, like square box o_O */
    r.append(" [shape=box, label=\"");

    r.append("\\["+getType()+"\\]");
    
    /* append the name of the variable */
    r.append("\\n"+name);

    r.append("\"];\n");

    return r;
  }

}
