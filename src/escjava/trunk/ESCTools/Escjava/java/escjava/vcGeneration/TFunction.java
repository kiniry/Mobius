package escjava.vcGeneration;

import java.lang.Class;
import java.io.PrintStream;
import java.util.Vector;
import java.util.Iterator;
import java.lang.StringBuffer;

import java.lang.ArrayIndexOutOfBoundsException;

abstract class TFunction extends TNode {
    
    protected /*@ non_null @*/ Vector sons = new Vector();
    
    /*@
      @ ensures \old(sons.size()) == sons.size()-1;
      @*/
    void addSon(/*@ non_null @*/ TNode n){
	sons.add(n);
    }

    /*@
      @ ensures index >= 0 && index <= sons.size()-1;
      @*/
    protected TNode getChildAt(int index){
	try { 
	    return (TNode)sons.elementAt(index); 
	}
	catch(ArrayIndexOutOfBoundsException e) { 
	    System.out.println("ArrayIndexOutOfBoundsException in escjava.vcGeneration.TFunction.getChildAt(int) "+e.getMessage());
	    return null; /* notice this default behaviour */
	}
    }

    public /*@ non_null @*/ StringBuffer toDot(){

	/* declaration of the node */
	StringBuffer r = new StringBuffer(dotId()); /* unique */

	r.append(" [label = \""+getShortName());

	// write the type (if exists)
	if(type!=null){
	    /* the old type is contained into the 'type' field which has
	       type 'typeInfo' ouf! */

	    r.append("\\n\\["+getType()+"\\]"); 
	}
    
	r.append("\"];\n");

	TNode nTemp = null;

	/* add all the sons */
	for(int i = 0; i <= sons.size() - 1; i++){

	    r.append(dotId()+" -> ");
	    
	    nTemp = getChildAt(i);
	    r.append(nTemp.dotId());

	    /* red arrow for variables, green one for value */
	    if(nTemp instanceof TName)
		r.append(" [color = red]");
	    else if(nTemp instanceof TLiteral)
		r.append(" [color = green]");

	    r.append(";\n");

	    /* recursive call on the sons */
	    r.append(nTemp.toDot());
	}

	return r;
    }

    protected void typeTree(){

	/* recursive call on the sons */
	for(int i = 0; i <= sons.size() - 1; i++)
	    getChildAt(i).typeTree();
  
    }

}
