package escjava.vcGeneration;

import java.lang.Class;
import java.io.PrintStream;
import java.util.Vector;
import java.util.Iterator;
import java.lang.StringBuffer;
import java.util.HashMap;
import java.util.Set;

abstract class TNode {

    /*@
      @ protected invariant (\forall TNode i,j ; i != j; i.id != j.id) &&
      @ (lastType >= 0) &&
      @ (typeProofSet ==> (lastType <= 1 && lastType <= 3)) &&
      @ (isroot ==> (this instanceof TRoot));
      @*/

    static /*@ spec_public @*/ protected PrintStream dotPs;
    protected int id;
    static protected int counter = 0;
    
    protected boolean isroot = false;
    public TypeInfo type = null;

    // internal representation of last type asked
    static /*@ spec_public @*/ protected int lastType = 0;
    static /*@ spec_public @*/ protected boolean typeProofSet = false;

    String label = null;
  
    /* map containing the variables names
     * When the tree is created, old name are entered as keys with 
     * a new {@link VariableInfo}(oldName, type) associated as value.
     * When the vc are generated, each time a variable is looked at, we look 
     * at this map. We look into the {@link VariableInfo} object associated.
     * If the renaming hasn't been done into this object, we do it.
     * If present, we use the already existing name.
     * Thus we will only rename one time and use previous value for next acccess.
     *
     * It handles multiple renaming because each {@link VariableInfo} object contains 
     * multiples fields for renaming (take a look at it).
     */
    static /*@ spec_public non_null @*/ protected HashMap variablesName = new HashMap();

    /*
     * map containing all the types used in the proof.
     * 
     * After calling {@link typeTree}, each node has his {@link TypeInfo} field 
     * not null. It points on a TypeInfo object which is a value of this HashMap.
     * Each TypeInfo object contains the old type, the pvs corresponding type,
     * and the sammy corresponding type.
     * The old type can be {reference, integer, boolean, type}.
     * The tree is typechecked after call to {@link SetOutputType} and
     * this map is filled with only the type asked.
     * Ie if you call setOutputType("unsortedPvs"), the tree will be typed
     * with the old type and the types for the unsorted logic of pvs.
     * If you make another call to setOutputType, it will add type the tree
     * for the new tree etc...
     */
    static /*@ spec_public non_null @*/ protected HashMap typesName = new HashMap();

    /*
     * We add some types that we know will be used to avoid looking
     * at the map typesName when we want to add it.
     */
    static TypeInfo $Reference = null;
    static TypeInfo $Type = null;
    static TypeInfo $DOUBLETYPE = null;
    static TypeInfo $boolean = null;
    static TypeInfo $char = null;
    static TypeInfo $double = null;
    static TypeInfo $Field = null;
    static TypeInfo $INTTYPE = null;
    static TypeInfo $integer = null;
    static TypeInfo $float = null;
    static TypeInfo $String = null;
    static TypeInfo $Time = null;

    static {
	$Reference = addType("%Reference");
	$Time = addType("%Time");
	$Type = addType("%Type");
	$boolean = addType("boolean");
	$char = addType("char");
	$DOUBLETYPE = addType("DOUBLETYPE");
	$double = addType("double"); //fixme
	$Field = addType("%Field");
	$INTTYPE = addType("INTTYPE");
	$integer = addType("integer");
	$float = addType("float");
	$String = addType("String");
    }

    public TNode(){

	// fixme :)
	//@ assert false;

	counter+=1;
	id = counter;
    }

    //   // fixme should not be declared
    //   abstract void addSon(TNode n);

    /*@
      @ requires type.equals("unsortedPvs") || type.equals("pvs") || type.equals("sammy");
      @ ensures (type.equals("unsortedPvs") <==> lastType == 1) &&
      @ (type.equals("sammy") <==> lastType == 2) && 
      @ (type.equals("pvs") <==> lastType == 3);
      @*/
    public void setOutputType(/*@ non_null @*/ String type){

	if(type.equals("unsortedPvs")){
	    typeProofSet = true;
	    lastType = 1;
	}
	if(type.equals("pvs")) {
	    typeProofSet = true;
	    lastType = 2;
	}
	else if(type.equals("sammy")){
	    typeProofSet = true;
	    lastType = 3;
	}
    
    }

    /*
     * This function add variable to the global map name.
     * @param oldName the old name.
     * @param type the type of the variable which has been infered from the old tree.
     *
     * @return the VariableInfo object representing this variables name 
     */
    /*@
      @ ensures variablesName.containsKey(oldName);
      @*/
    static public /*@ non_null @*/ VariableInfo addName(/*@ non_null @*/ String oldName, /*@ non_null @*/ String type){

	if(!variablesName.containsKey(oldName)){
	    // we will do the renaming when necessary (look at {@link VariableInfo})
      
	    TypeInfo ti = null;

	    /*
	     * We retrieve the type if necessary.
	     */
	    if(type!=null)
		ti = TNode.addType(type);
	    else
		System.err.println("Warning, adding variable named "+oldName+" with no types");

	    //@ assert typesName.containsKey(type);
	    variablesName.put(oldName, new VariableInfo(oldName, ti));
	}
	//++
	else {

	    // debugging stuff that checks the new type is the same as the previous on
	    if(type!=null){
		
		VariableInfo vi = (VariableInfo)variablesName.get(oldName);
      		if(vi.type != typesName.get(type)) {
		    
		    System.out.println("escjava/vcGeneration/TNode::addVariable *** Warning ***");
		    System.out.print("You're trying to add a variable named "+oldName+" whith type "+type.toString()+" which has been already stored with the type "+vi.type.toString() +" to the proof tree");
		}
	    }

	}

	//@ assert variablesName.containsKey(oldName);

	/* we return the node which represents this variable.
	 * Note that if this oldName wasn't present in the hashMap
	 * the node returned is the one added created with TName node = new TName(oldName);
	 */
	return (VariableInfo)variablesName.get(oldName);

	//++
    }

    /*
     * This function add type to the global map .
     * @param oldName the old name.
     *
     * @return the node pointing on that variable (can already exist if this add is
     * useless, in this case we return the previous TypeInfo representing this type).
     */
    /*@
      @ ensures typesName.containsKey(oldType);
      @*/
    static public /*@ non_null @*/ TypeInfo addType(/*@ non_null @*/ String oldType){

	if(!typesName.containsKey(oldType)){
	    // we will do the renaming when necessary (look at {@link TypeInfo})
      
	    TypeInfo ti = new TypeInfo(oldType);
	    typesName.put(oldType, ti);

	    //@ assert typesName.containsKey(oldType);

	    return ti;
	}
	else {
	    //@ assert typesName.containsKey(oldType);

	    return (TypeInfo)typesName.get(oldType);
	}    
      
    }

    abstract /*@ non_null @*/ StringBuffer toDot();

    /* dot id which is unique because of adding 
       'id' to the name of the node */
    protected /*@ non_null @*/ String dotId(){

	/* escjava.vcGeneration.Tabc => r = abc */
	String r = getClass().getName().substring(22);
	r = r+id;

	return r;
    }

    // to avoid printing eachtime 'escjava.dsaParser.' and remove first 'T'
    protected /*@ pure non_null @*/ String getShortName(){
	return getClass().getName().substring(22);
    }

    /*@
      @ requires typeProofSet;
      @ ensures type != null;
      @*/
    abstract protected void typeTree();

    /*
     * Add the type if not present to the global map of type
     * and fill the correct field with it.
     */
    protected void setType(String s, boolean sure){
	type = TNode.addType(s);
    }

    protected void setType(TypeInfo type, boolean sure){
	
	if(this instanceof TName){
	    TName m = (TName)this;

	    //@ assert m.type == null;

	    // retrieve current type;
	    if(!variablesName.containsKey(m.name)) {
		System.err.println("escjava::vcGeneration::TNode::setType");
		System.err.println("You're manipulating a TName ("+m.name+") node, yet the name isn't in the global map 'variablesName'");
	    }
	    // take care no else here
	    
	    VariableInfo vi = (VariableInfo)variablesName.get(m.name);
	    
	    if(vi.type == null) {// we set it
		vi.type = type;
	    }
	    else {
		if(vi.type != type) {// inconsistency
		    if(vi.typeSure) // we don't change it
			System.err.println("Variable named "+m.name+", has type "+vi.type.old+" yet you try to change it to "+type.old);
		    else {
			System.err.println("Changing type of "+m.name+" (which was "+vi.type.old+") to "+type.old);
			vi.type = type;
		    }
		}
		    
	    }
	}
	else {
	    if(this.type != null) {
		// we compare the existing type
		if(this.type != type) { // The two types are not equals
		    // inconsistancy
		    System.err.println("*** Warning, typechecking inconsistancy, "+this.toString() +"has type "+this.type.old+ "but you're trying to set his type to "+type.old);
		}
	    }
	    else  // type is null qué pasa ?
		System.err.println("Node  "+this.toString()+" has no type");
				   
	}
    }


    /*
     * return the type of the node according to the type of proof asked
     * or "?" if type isn't known.
     */
    /*@
      @ requires typeProofSet;
      @*/
    public /*@ non_null @*/ String getType(){

	if(this instanceof TName){
	    // retrieve the type in the global variablesNames map
	    TName m = (TName)this;

	    //@ assert m.type == null;

	    // retrieve current type;
	    if(!variablesName.containsKey(m.name)) {
		System.err.println("escjava::vcGeneration::TNode::setType");
		System.err.println("You're manipulating a TName ("+m.name+") node, yet the name isn't in the global map 'variablesName'");
	    }
	    // take care no else here
	    
	    VariableInfo vi = (VariableInfo)variablesName.get(m.name);

	    if(vi.type == null)
		return "?";
	    else {
		TypeInfo ti = vi.type;

		switch(lastType){
		case(0):
		    return ti.old;
		case(1):
		    return ti.getUnsortedPvs();
		case(2):
		    return ti.getPvs();
		case(3):
		    return ti.getSammy();
		default :
		    System.err.println("Error when calling escjava::vcGeneration::TNode::getType, type of the proof is not correctly set");
		    return "";
		}
	    }
	    
	}
	else {
	    if(this.type == null)
		return "?";

	    switch(lastType){
	    case(0):
		return this.type.old;
	    case(1):
		return this.type.getUnsortedPvs();
	    case(2):
		return this.type.getPvs();
	    case(3):
		return this.type.getSammy();
	    default :
		System.err.println("Error when calling escjava::vcGeneration::TNode::getType, type of the proof is not correctly set");
		return "";
	    }
	}
	
    }

    public String toString(){
	if(type!=null)
	    return getShortName()+id+", "+type.old;
	else
	    return getShortName()+id;
    }

    static public void printInfo(){
    
	// print all variables and their renaming in a nice way
	Set keySet = variablesName.keySet();

	Iterator iter = keySet.iterator();
	String keyTemp = null;
	VariableInfo viTemp = null;

	System.out.println("\n=== List of variables ===");
	System.out.println("[oldName, unsortedPvsName, pvsName, sammyName : oldType ]");

	while(iter.hasNext()){
      
	    try {
		keyTemp = (String)iter.next();
	    }
	    catch (Exception e){
		System.err.println(e.getMessage());
	    }
	    viTemp = (VariableInfo)variablesName.get(keyTemp);

	    /* output informations in this format : oldName, pvsUnsortedName,
	     * pvsName, sammyName, type.
	     */
	    if(viTemp.type!=null) // fixme
		System.out.println("["+viTemp.oldName+", "+viTemp.getUnsortedPvsName()+", "+viTemp.getPvsName()+", "+viTemp.getSammyName()+" : "+viTemp.type.old+"]"); 
	    else
		System.out.println("["+viTemp.oldName+", "+viTemp.getUnsortedPvsName()+", "+viTemp.getPvsName()+", "+viTemp.getSammyName()+" : ?type? ]"); 
	}

	keySet = typesName.keySet();
	iter = keySet.iterator();
	TypeInfo tiTemp = null;
    
	System.out.println("\n=== List of type      ===\n");

	while(iter.hasNext()){
      
	    try {
		keyTemp = (String)iter.next();
	    }
	    catch (Exception e){
		System.err.println(e.getMessage());
	    }
	    tiTemp = (TypeInfo)typesName.get(keyTemp);

	    /* output informations in this format : old, pvsUnsorted,
	     * pvs, sammy.
	     */

	    System.out.println("["+tiTemp.old+", "+tiTemp.getUnsortedPvs()+", "+tiTemp.getPvs()+", "+tiTemp.getSammy()+"]"); 
	}

	System.out.print("\n");
    }
}




