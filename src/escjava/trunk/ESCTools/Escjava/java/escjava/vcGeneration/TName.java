package escjava.vcGeneration;

class TName extends TVariable {

    /*@ non_null @*/ String name;

    /*
     * type is supposed to be one of the object that is statically
     * initialized in TNode, like $Reference, $Type etc...
     */
    protected TName(/*@ non_null @*/ String name, TypeInfo type){
	this.name = name;
	
	if(type!=null)
	    this.type = type;
    }

  public /*@ non_null @*/ StringBuffer toDot(){

    /* dot id which is unique because of adding 
     'id' to the name of the node */
    StringBuffer r = new StringBuffer(dotId());

    /* add fancy stuff, like square box o_O */
    r.append(" [shape=box, label=\"");

    /* add the type if !null 
       else display the name of the class : 'Name'
    */
    if(type!=null)
	r.append("\\["+getType()+"\\]");
    else
	r.append(getShortName());

    /* append the name of the variable */
    r.append("\\n"+name);

    r.append("\"];\n");

    return r;
  }

    protected void typeTree(){

	if(type!=null) {
	    if(!variablesName.containsKey(name))
		System.err.println("escjave::vcGeneration::TName::typeTree, Error when retrieving variableInfo object of variable "+name);
	    else {
		/* set the type into the global variable name
		 * so that the other TName node representing the same 
		 * variable can use it
		 */
		VariableInfo vi = (VariableInfo)variablesName.get(name);

		if(vi.type != null){
		    /*
		     * check that the type we want to add isn't contradictory
		     * with the one already present.
		     */
		    if(!vi.type.equals(this.type))
			System.out.println("Error when setting type of variable named "+name+", type previously stored is "+vi.type.old+" and types of this node is "+this.type.old);
		}
		else
		    vi.type = this.type; 
		// the global type wasn't set,
		// we set it
	    }
	}
	else {
	    /* retrieve the type in the global map */
	    type = (TypeInfo)(((VariableInfo)variablesName.get(name)).type);

	    if(type == null)
		System.out.println("Variable "+name+" wasn't typed after 1 passage...");
	    
	}
	
    }

}
