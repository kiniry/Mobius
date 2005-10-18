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
      @ (isroot ==> (this instanceof TRoot)) &&
      @ (parent != null || this instanceof TRoot);
      @*/

    // fixme explain it in the doc
    static /*@ spec_public @*/ protected PrintStream dotPs;
    protected int id;
    static protected int counter = 0;
    
    protected boolean isroot = false;
    public TypeInfo type = null;

    // internal representation of last type asked
    static /*@ spec_public @*/ protected int lastType = 0;
    static /*@ spec_public @*/ protected boolean typeProofSet = false;

    protected TFunction parent = null;

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
    static /*@ spec_public non_null @*/ protected HashMap variablesName = null;

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
    static /*@ spec_public non_null @*/ /* protected */ HashMap typesName = null;

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
    static TypeInfo $Path = null;

    public TNode(){

	// fixme :)
	//@ assert false;

	counter+=1;
	id = counter;
    }

    
    // init every both variable and type map.
    static public void init (){
	typesName = new HashMap();
	variablesName = new HashMap();

	// Predefined types

	$Reference = addType("%Reference", "S", "Reference", "?");
	$Time = addType("%Time", "S", "Time", "?");
	$Type = addType("%Type", "S", "ReferenceType", "?");
	$boolean = addType("boolean", "S", "Boolean", "?");
	$char = addType("char", "S", "T_char", "?");
	$DOUBLETYPE = addType("DOUBLETYPE", "S", "ContinuousNumber", "?"); // fixme, is it JavaNumber or BaseType ?
	$double = addType("double", "S", "ContinuousNumber", "?"); //fixme
	$Field = addType("%Field", "S", "Field", "?"); // fixme there's a lot of different fields in the pvs logic, I need to capture that
	$INTTYPE = addType("INTTYPE", "S", "T_int", "?"); //fixme like DOUBLETYPE
	$integer = addType("integer", "S", "DiscreteNumber", "?"); //fixme
	$float = addType("float", "S", "ContinuousNumber", "?");
	$Path = addType("%Path", "S", "Path", "?"); // used to modelize different ways
	// of terminating a function
	//$String = addType("String", "S", "String", "?"); fixme, does this type appears in original proof ?


	// Predefined variables name
	// variables used by the old proof system and that we still need
	addName("ecReturn", "%Path", "ecReturn", "preDef?ecReturn", "ecReturn");
	addName("ecThrow", "%Path", "ecThrow", "preDef?ecThrow", "ecThrow");
	addName("XRES", "%Reference", "%XRES", "preDef?XRes", "XRES");
	
    }

    /*@
      @ requires type.equals("unsortedPvs") || type.equals("pvs") || type.equals("sammy");
      @ ensures (type.equals("unsortedPvs") <==> lastType == 1) &&
      @ (type.equals("pvs") <==> lastType == 2) &&
      @ (type.equals("sammy") <==> lastType == 3);
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

    /*@
      @ requires type.equals("unsortedPvs") || type.equals("pvs") || type.equals("sammy");
      @ requires typeProofSet;
      @*/
    protected void generateDeclarations(/*@ non_null @*/ StringBuffer s){
	
	Set keySet = variablesName.keySet();

	Iterator iter = keySet.iterator();
	String keyTemp = null;
	VariableInfo viTemp = null;
	TypeInfo tiTemp = null;

	/*
	 * Needed to avoid adding a comma after last declaration. As some declaration can be skipped
	 * it's easier to put comma before adding variable (thus need for testing firstDeclaration
	 * instead of last one)
	 */
	boolean firstDeclarationDone = false;

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
	    if(viTemp.type!=null) {
		
		switch(lastType){
		case 1:
		    if(firstDeclarationDone && !viTemp.getUnsortedPvs().equals("%NotHandled"))
			s.append(",\n");

		    if(!viTemp.getUnsortedPvs().equals("%NotHandled")) { // skipping non handled variables
			s.append(viTemp.getUnsortedPvs()+" : "+viTemp.type.getUnsortedPvs());

			if(!firstDeclarationDone)
			    firstDeclarationDone = true;
		    }

		case 2 : 
		    if(firstDeclarationDone && !viTemp.getPvs().equals("%NotHandled"))
			s.append(",\n");

		    if(!viTemp.getPvs().equals("%NotHandled")) { // skipping non handled variables
			s.append(viTemp.getPvs()+" : "+viTemp.type.getPvs());

			if(!firstDeclarationDone)
			    firstDeclarationDone = true;
		    }

		    break;

		case 3 :
		    if(firstDeclarationDone && !viTemp.getSammy().equals("%NotHandled"))
			s.append(",\n");

		    if(!viTemp.getSammy().equals("%NotHandled")) { // skipping non handled variables
			s.append(viTemp.getSammy()+" : "+viTemp.type.getSammy());

			if(!firstDeclarationDone)
			    firstDeclarationDone = true;
		    }

		default :
		    TDisplay.err(this, "generateDeclarations", "Type is equal to "+lastType+" which isn't ok");
		    
		}
	    }
	    else // fixme test that it nevers happen
		TDisplay.warn(this, "generateDeclarations", "Type of variable "+keyTemp+" is not set when declarating variables for the proof, skipping it...");
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
    static public /*@ non_null @*/ VariableInfo addName(/*@ non_null @*/ String oldName, /*@ non_null @*/ String type, String unsortedPvs, String pvs, String sammy){

	if(!variablesName.containsKey(oldName)){
	    // we will do the renaming when necessary (look at {@link VariableInfo})
      
	    TypeInfo ti = null;

	    /*
	     * We retrieve the type if necessary.
	     */
	    if(type!=null)
		ti = TNode.addType(type);
	    else
		TDisplay.warn("TNode", "addName", "Adding variable named "+oldName+" with no types");

	    //@ assert typesName.containsKey(type);
	    variablesName.put(oldName, new VariableInfo(oldName, ti, unsortedPvs, pvs, sammy));
	}
	//++
	else {

	    // debugging stuff that checks the new type is the same as the previous on
	    if(type!=null){
		
		VariableInfo vi = (VariableInfo)variablesName.get(oldName);
      		if(vi.type != typesName.get(type)) {
		    
		    TDisplay.warn("TNode", "addName", "You're trying to add a variable named "+oldName+" whith type "+type.toString()+" which has been already stored with the type "+vi.type.toString() +" to the proof tree");
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

    static public /*@ non_null @*/ VariableInfo addName(/*@ non_null @*/ String oldName, /*@ non_null @*/ String type){
	return addName(oldName, type, null, null, null);
    }

    /*
     * return the {@link VariableInfo} object associated with this name
     */
    //@ requires variablesName.contains(s);
    static /*@ non_null @*/ VariableInfo getVariableInfo(/*@ non_null @*/ String name){
	return (VariableInfo)variablesName.get(name);
    }

    /*
     * return the {@link VariableInfo} object associated of the caller which
     * must be an instance of TName.
     */
    //@ requires variablesName.contains(s);
    /*@ non_null @*/ VariableInfo getVariableInfo(){

	//@ assert this instanceof TName;

	if(! (this instanceof TName)) {
	    TDisplay.err(this, "getVariableInfo()", "Warning calling getVariableInfo on a non TName Node");
	    return null;
	}
	else {
	    TName n = (TName) this;
	    return getVariableInfo(n.name);
	}
	
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
    static public /*@ non_null @*/ TypeInfo addType(/*@ non_null @*/ String oldType, String unsortedPvs, String pvs, String sammy){

	if(!typesName.containsKey(oldType)){
	    // we will do the renaming when necessary (look at {@link TypeInfo})
      
	    TypeInfo ti = new TypeInfo(oldType, unsortedPvs, pvs, sammy);
	    typesName.put(oldType, ti);

	    //@ assert typesName.containsKey(oldType);

	    return ti;
	}
	else {
	    //@ assert typesName.containsKey(oldType);

	    return (TypeInfo)typesName.get(oldType);
	}    
      
    }

    static public /*@ non_null @*/ TypeInfo addType(/*@ non_null @*/ String oldType){
	return TNode.addType(oldType, null, null, null);
    }

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
		TDisplay.err(this, "setType(TypeInfo, boolean)", "You're manipulating a TName ("+m.name+") node, yet the name isn't in the global map 'variablesName'");
	    }
	    // take care no else here
	    
	    VariableInfo vi = (VariableInfo)variablesName.get(m.name);
	    
	    if(vi.type == null) {// we set it
		vi.type = type;
	    }
	    else {
		if(vi.type != type) {// inconsistency
		    if(vi.typeSure) // we don't change it
			TDisplay.err(this, "setType(TypeInfo, boolean)", "Variable named "+m.name+", has type "+vi.type.old+" yet you try to change it to "+type.old);
		    else {
			TDisplay.warn(this, "setType(TypeInfo, boolean)", "Changing type of "+m.name+" (which was "+vi.type.old+") to "+type.old);
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
		    TDisplay.warn(this, "setType(TypeInfo, boolean)", "Typechecking inconsistancy, "+this.toString() +"has type "+this.type.old+ "but you're trying to set his type to "+type.old);
		}
	    }
	    else  // type is null qué pasa ?
		TDisplay.err(this, "setType(TypeInfo, boolean)", "Node "+this.toString()+" has no type");
				   
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
		TDisplay.err(this, "getType", "You're manipulating a TName ("+m.name+") node, yet the name isn't in the global map 'variablesName'");
	    }
	    // take care no else here
	    
	    VariableInfo vi = (VariableInfo)variablesName.get(m.name);

	    if(vi.type == null)
		return "?";
	    else {
		TypeInfo ti = vi.type;

		String result = "";
		/*
		 * Handle double type here
		 */
		if(ti == $Field){ // variables may have a second type;
		    if(vi.getSecondType() != null) {

			/*
			 * fixme : explanations needed here, tricky stuff.
			 */

			TypeInfo ti2 = vi.getSecondType();
			VariableInfo vi2 = getVariableInfo(ti2.old);

			switch(lastType){
			case(0):
			    result = vi2.old + "\\n";
			    break;
			case(1):
			    result = vi2.getUnsortedPvs() + "\\n";
			    break;
			case(2):
			    result = vi2.getPvs() + "\\n";
			    break;
			case(3):
			    result = vi2.getSammy() + "\\n";
			    break;
			default :
			    TDisplay.err(this, "getType", "Error when calling escjava::vcGeneration::TNode::getType, type of the proof is not correctly set");
			    return "";
			}

		    }
			
		}

		switch(lastType){
		case(0):
		    result = result + ti.old;
		    break;
		case(1):
		    result = result + ti.getUnsortedPvs();
		    break;
		case(2):
		    result = result + ti.getPvs();
		    break;
		case(3):
		    result = result + ti.getSammy();
		    break;
		default :
		    TDisplay.err(this, "getType", "Error when calling escjava::vcGeneration::TNode::getType, type of the proof is not correctly set");
		    return "";
		}

		return result;
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
		TDisplay.err(this, "getType", "Error when calling escjava::vcGeneration::TNode::getType, type of the proof is not correctly set");
		return "";
	    }
	}
	
    }

    /*
     * Return the typeInfo associated with this node. It can just be
     * the 'type' field for non instance of TName. Or in the case
     * of TName node, we retrieve it in the global map.
     */
    public TypeInfo getTypeInfo(){

	if(!(this instanceof TName))
	    return this.type;
	else { //retrieve the type in the map

	    TName m = (TName)this;

	    //@ assert m.type == null;

	    // retrieve current type;
	    if(!variablesName.containsKey(m.name)) {
		TDisplay.err(this, "getType", "You're manipulating a TName ("+m.name+") node, yet the name isn't in the global map 'variablesName'");
	    }
	    // take care no else here
	    
	    VariableInfo vi = (VariableInfo)variablesName.get(m.name);

	    //++
// 	    if(vi.type != null)
// 		System.out.println("returning "+vi.type.old+" for "+this.toString());
	    //++

	    // can be null
	    return vi.type;
	}

    }

    public String toString(){
	if(type!=null)
	    return getShortName()+id+", "+type.old;
	else
	    return getShortName()+id;
    }

    abstract public void accept(/*@ non_null @*/ TVisitor v);

    static public void printInfo(){
    
	// print all variables and their renaming in a 'nice' way
	Set keySet = variablesName.keySet();

	Iterator iter = keySet.iterator();
	String keyTemp = null;
	VariableInfo viTemp = null;

	System.out.println("\n=== List of variables ===");
	System.out.println("[oldName, unsortedPvsName, pvsName, sammyName : oldType]\n");

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
		System.out.println("["+viTemp.old+", "+viTemp.getUnsortedPvs()+", "+viTemp.getPvs()+", "+viTemp.getSammy()+" : "+viTemp.type.old+"]"); 
	    else
		System.out.println("["+viTemp.old+", "+viTemp.getUnsortedPvs()+", "+viTemp.getPvs()+", "+viTemp.getSammy()+" : ?type? ]"); 
	}

	keySet = typesName.keySet();
	iter = keySet.iterator();
	TypeInfo tiTemp = null;
    
	System.out.println("\n=== List of type      ===");
	System.out.println("[old, unsortedPvs, Pvs, Sammy]\n");

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




