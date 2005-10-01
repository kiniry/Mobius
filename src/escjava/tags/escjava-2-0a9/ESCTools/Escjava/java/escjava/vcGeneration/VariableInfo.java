package escjava.vcGeneration;

import java.util.Iterator;
import java.util.Set;
import java.util.HashMap;

import java.util.regex.Pattern;
import java.util.regex.Matcher;

class VariableInfo {

    /*
     * README :
     *
     * This class is used to contain renaming of variables.
     * For each variable a VariableInfo object is created.
     *
     * If you want to change the way variables are renamed, just change 
     * {@link pvsRename} or {@link sammyRename} or add
     * a function at the end.
     */

    /*@ non_null @*/ String old = null;
    TypeInfo               type = null;
    private String unsortedPvs  = null;
    private String pvs          = null;
    private String sammy        = null;
    public boolean typeSure     = false;

    /*
     * This last field wasn't planned intially. 
     * But it is necessary when some variables have two types
     * like for a classe like :
     *
     * class A {

     int i1;

     }
     *
     * Then the variable i1 must have as first type "%Field"
     * and "integer" two.
     */
    private TypeInfo secondType = null;
	
    /*
     * When we call this variable, we know his old type, so we gave it.
     */
    public VariableInfo(/*@ non_null @*/ String old, TypeInfo type){
	this.old = old;
	this.type = type;
    }

    /*
     * Constructor for specifying the renaming of the variable.
     */
    public VariableInfo(/*@ non_null @*/ String old, TypeInfo type, /*@ non_null @*/ String unsortedPvs, /*@ non_null @*/ String pvs, /*@ non_null @*/ String sammy){
    this.old = old;
    this.type = type;
    this.unsortedPvs = unsortedPvs;
    this.pvs = pvs;
    this.sammy = sammy;
  }

    public void setSecondType(/*@ non_null @*/ TypeInfo type){
	
	/*
	 * do some control
	 */ 
	if(secondType!=null) {
	    if(secondType != type)
		System.err.println("Inconsistancy, changing type of a field named "+old+" from "+secondType.old+" to "+type.old);
	}
	else
	    secondType = type;
	
    }

    public TypeInfo getSecondType(){
	return secondType;
    }

    public /*@ non_null @*/ String getUnsortedPvs(){

	if(type != TNode.$Type){
	    if(unsortedPvs == null)
		unsortedPvsRename();
	    
	    return unsortedPvs;
	}
	else return type.getUnsortedPvs();
    }

    public /*@ non_null @*/ String getPvs(){

	if(type != TNode.$Type){
	    if(pvs == null)
		pvsRename();

	    return pvs;
	}
	else {
	    /*

	    When variable is a type, we first have to check if it's in the type table.
	    If yes, we take the name here (it's the case with predefined types like INTYPE, integer, Reference etc...

	    Else it's normally a user defined Type

	    */
	    
	    Set keySet = TNode.typesName.keySet();
	    Iterator iter = keySet.iterator();
	    TypeInfo tiTemp = null;
	    String keyTemp = null;

	    while(iter.hasNext()){
      
		try {
		    keyTemp = (String)iter.next();
		}
		catch (Exception e){
		    System.err.println(e.getMessage());
		}
		tiTemp = (TypeInfo)TNode.typesName.get(keyTemp);

		if(tiTemp.old.equals(old)) {
		    return tiTemp.getPvs();
		}
		    
	    }

	    System.err.println("Warning in escjava.java.vcGenerator.VariableInfo.getPvs(), considering "+old+" as a user defined type, or a not (yet) handled variable.");

	    pvsRename();

	    return pvs;
	}
	
    }
 
    public /*@ non_null @*/ String getSammy(){

	if(type != TNode.$Type){
	    if(sammy == null)
		sammyRename();

	    return sammy;
	}
	else return type.getSammy();
    }

    public /*@ non_null @*/ String getSimplify(){

	/*
	 * This method is special since <explanation>
	 * FIXME
	 */

	if(type != TNode.$Type)
	    return old;
	
	else {
	    if(old.equals("boolean"))
	       return "T_bool"; // fixme not sure
	    else if(old.equals("char"))
		return "T_char";
	    else if(old.equals("DOUBLETYPE"))
		return "T_double";
	    else if(old.equals("double"))
		return "T_double";
	    else if(old.equals("JMLDataGroup"))
		return "|T_org.jmlspecs.lang.JMLDataGroup|";
	    else if(old.equals("INTTYPE"))
		return "T_int";
	    else if(old.equals("integer"))
		return "T_int";
	    else if(old.equals("Unknown tag <242>"))
		return "T_anytype";
	    else {
		if(old.startsWith("java.")) //check if in the form java.x.y 
		    return "T_"+old;
		else {
		    System.err.println("Type not handled in escjava.vcGeneration.VariableInfo.getSimplify() "+old);
		    System.err.println("Considering it as a user defined type");
		    return "T_"+old;
		}
	    }
	}
    }

    public /*@ non_null @*/ String toString(){
	return "["+old+", "+type+", "+pvs+", "+sammy+"]";
    }

    // fixme, does nothing atm
    /*@
      @ ensures unsortedPvs != null;
      @*/
    private void unsortedPvsRename(){
	unsortedPvs = old;
    }

    /*@
      @ ensures pvs != null;
      @*/
    private void pvsRename(){

	// definitions of different regexp used.
	Pattern p1 = Pattern.compile("\\|(.*):(.*)\\.(.*)\\|");
	Matcher m1 = p1.matcher(old);
	
	// <variables not handled>
	Pattern p2 = Pattern.compile("Unknown tag <.*>");
	Matcher m2 = p2.matcher(old);
	
	Pattern p3 = Pattern.compile("\\|brokenObj<.*>\\|");
	Matcher m3 = p3.matcher(old);
	// </variables not handled>

	String name = null;
	String line = null;
	String column = null;

	int i = 0;

	//System.out.println("Performing regular expression matching against "+old+" ");

	/*
	  This case is done first because some variables not handled are "%Type" ones
	  and thus otherwise they will be matched by the next if construct
	*/
	if(m2.matches() || m3.matches() || old.equals("brokenObj")) { // variable is not handled yet, ask David Cok about
	    // some things
	    pvs = "%NotHandled"; 
	}

	// <case 1>
	/*
	  If variable's a type, we must prefix his renaming by userDef?.
	  Why ?
	  Because if the user defined a type named 'Reference', otherwise we will use is as it
	  in the proof and it will interfer with our predefined types.

	  Since '?' isn't a valid character in the java notation and is Ok for pvs,
	  we use it to make the difference.
	*/
	else if(type == TNode.$Type){
	    System.err.println("Warning in escjava.java.vcGeneration.VariableInfo.pvsRename() : considering "+old+" as a user defined type.");

	    // renaming done here
	    pvs = "userDef?"+old;
	}
	// </case 1>

	// <case 2>, capturing |y:8.31|
	else if(m1.matches()){
	    //@ assert m.groupCount() == 3;

	    if(m1.groupCount() != 3)
		System.err.println("Error in escjava.java.vcGeneration.VariableInfo.pvsRename : m.groupCount() != 3");

	    for( i = 1; i <= m1.groupCount(); i++) {

		if(m1.start(i) == -1 || m1.end(i) == -1)
		    System.err.println("Error in escjava.java.vcGeneration.VariableInfo.pvsRename : return value of regex matching is -1");
		else {
		    
		    String temp = old.substring(m1.start(i),m1.end(i));
		    //@ assert temp != null;

		    switch(i){ 
		    case 1 :
			name = temp;
			//@ assert name != null;
			break;
		    case 2:
			line = temp;
			//@ assert line != null;
			break;
		    case 3:
			column = temp;
			//@ assert column != null;
			break;
		    default :
			System.err.println("Error in escjava.java.vcGeneration.VariableInfo.pvsRename : switch call incorrect, switch on value "+i);
			break;
		    }
		} // no error in group
		
	    } // checking all group

	    /* renaming done here, if you want the way it's done
	       (for pattern like |y:8.31|)
	       do it here. */
	    pvs = name+"_"+line+"_"+column;

	} // </case 2>
	else {
	    pvs = old; // FIXME handle everything
	} // regexp didn't match

    }

    // fixme, does nothing atm
    /*@
      @ ensures sammy != null;
      @*/
    private void sammyRename(){
	sammy = old;
    }

}
