package escjava.vcGeneration;

import java.io.IOException;

public class TName extends TVariable {

    /*@ non_null @*/public String name;

    /**
     * type is supposed to be one of the object that is statically
     * initialized in TNode, like $Reference, $Type etc...
     */
    protected TName(/*@ non_null @*/String name) {
        this.name = name;
    }

    public void accept(/*@ non_null @*/TVisitor v) throws IOException {
        v.visitTName(this);
    }
    protected void typeTree(){
    	// lets try to fetch our type...
    	if(type == null) {
    		VariableInfo vi = TNode.getVariableInfo(name);
    		type = vi.type;
    	}
    }
    
    protected void setType(TypeInfo type, boolean sure){
    	
	    TName m = (TName)this;
	    //@ assert m.type == null;

	    // retrieve current type;
	    if(!variablesName.containsKey(m.name)) {
	    	TDisplay.err(this, "setType(TypeInfo, boolean)", "You're manipulating a TName ("+m.name+") node, yet the name isn't in the global map 'variablesName'");
	    }
	    // take care no else here
	    
	    VariableInfo vi = (VariableInfo)variablesName.get(m.name);
	    
	    if(vi.type == null) {// we set it
	    	vi.type = type;
	    }
	    else {
			if(!vi.type.equals(type)) {// inconsistency
			    if(vi.typeSure) // we don't change it
			    	TDisplay.err(this, "setType(TypeInfo, boolean)", "Variable named "+m.name+", has type "+vi.type.old+" yet you try to change it to "+type.old);
			    else {
			    	if(type == $Reference) {
			    		// no we won't change it !!!
			    		TDisplay.warn(this, "setType(TypeInfo, boolean)", "I won't change the type of "+m.name+" (which was "+vi.type.old+") to this silly type : "+type.old);
			    	}
			    	else {
			    		TDisplay.warn(this, "setType(TypeInfo, boolean)", "Changing type of "+m.name+" (which was "+vi.type.old+") to "+type.old);
			    		vi.type = type;
			    	}
			    }
			}	    
	    }
	    this.type = vi.type;
   }
}



