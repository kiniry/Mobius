package escjava.vcGeneration;

import java.lang.Class;
import java.io.PrintStream;
import java.util.Vector;
import java.util.Iterator;
import java.lang.StringBuffer;

import java.lang.ArrayIndexOutOfBoundsException;

abstract class TFunction extends TNode {
    
    /*
     * This field is not protected because we can remove childs
     * in TProofSimplifier.java
     */
    /*@ non_null @*/ Vector sons = new Vector();
    
    /*@
      @ ensures \old(sons.size()) == sons.size()-1;
      @*/
    void addSon(/*@ non_null @*/ TNode n){
	sons.add(n);

	//++
	if(n.parent != null)
	    TDisplay.err(this, "addSon", "node already have a parent");
	//++
	else
	    n.parent = this;
    }

    /*@
      @ ensures index >= 0 && index <= sons.size()-1;
      @*/
    protected TNode getChildAt(int index){
	try { 
	    return (TNode)sons.elementAt(index); 
	}
	catch(ArrayIndexOutOfBoundsException e) { 
	    TDisplay.err(this, "getChildAt", "ArrayIndexOutOfBoundsException"+e.getMessage());
	    return null; /* notice this default behaviour */
	}
    }

    protected void typeTree(){

	/* recursive call on the sons */
	for(int i = 0; i <= sons.size() - 1; i++)
	    getChildAt(i).typeTree();
  
    }

}
