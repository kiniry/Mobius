/*
 * Created on Mar 11, 2005
 *
 * TODO To change the template for this generated file go to
 * Window - Preferences - Java - Code Style - Code Templates
 */

/**
 * @author tdupont
 *
 * TODO To change the template for this generated type comment go to
 * Window - Preferences - Java - Code Style - Code Templates
 */



import java.util.*;
import java.util.regex.*;


//Definition of the node type
import org.w3c.dom.Node;



//Class representing the instanciated to represent a XML property
// described in UPPAAL as a template
public class Property extends OrientedGraph implements Comparable , Cloneable{

	public String propertyName;
	public LinkedList localVariables;	//LinkedList of Variables
	public LinkedList parameters;		//LinkedList of Variables
	private boolean succeeded;
	
	//used for synthesis : Global Modifiers
	private static LinkedList ModifiedListGlobalVar	; 		//store at synthesis time the global Var used
	private static LinkedList updateMethodListGlobalVar ;	//stores in the same order, the body of the method generated for modification
	private static LinkedList updateMethodannotationList ; 	//stores in the same order, the annotation associated
	private static LinkedList updateMethodelseAnnotationList; //stores in the same order, info to generate the 'else' annotation

	
	Property() {
		super();
		//Outils o = Outils.outilsFactory();
		propertyName = "";		
		localVariables = new LinkedList();                                                                                                   		 
		parameters = new LinkedList(); 
		succeeded = false;
	}
	Property(Node template) {
		
		super();
		
		//Outils o = Outils.outilsFactory();
		propertyName = "";		
		localVariables = new LinkedList();                                                                                                   		 
		parameters = new LinkedList();  	
		ModifiedListGlobalVar	   = new LinkedList(); 
		updateMethodListGlobalVar  = new LinkedList();	
		updateMethodannotationList = new LinkedList(); 
		updateMethodelseAnnotationList= new LinkedList(); 		
		
		
		//build list of states and transitions out of the DOM
		LinkedList states = new LinkedList();			
		LinkedList transitions = new LinkedList();
		succeeded = extractProperty(template, states, transitions);
		State init = modifyTransitionRef(states, transitions);
		
		
		// Attach these list of element
		addEdges(transitions);
		addNodes(states);
		setInitialNode(init);
		//System.err.println("End xml parsing");
	}
	
	// Function used only by the constructor
	private boolean extractProperty(Node node, LinkedList states, LinkedList transitions){
		/* Functions used to extract property, and preparing it ready for synthesis*/
		//extract property given under the form of a DOM Node
		
		Outils o = Outils.outilsFactory();
		Node child;
		State state;
		Transition transition;
		String string;
		int i, j;
		
		
		//General configuration of the template node to be recieved as param
		/*
		+template
		|--- (Text=null)
		|---+name
			|--- value 
		|---+parameters
			|--- value
		|--- declaration
		|---+location (id=value)
			|---+name
				|--- value
			|---+label (kind= invariant)
				|--- value
		    |--- init (ref=id)
		|---+transition
			|--- source (ref = Value)
			|--- target (ref = Value)
			|---+label (kind= (synchronisation | update |guard))
				|--- value				
			|---(nail) 
		//*/
		
		
		/********  Verifications  ********/
		//if node is a contains a template node
		if (!(o.Name(node).toLowerCase().compareTo("template") == 0
				&& o.Type(node).toLowerCase().compareTo("element") == 0)) return false;
		/********************************/
		
		
		for (i=0 ; i< o.childCount(node) ; i++ ) {
			child = o.child(node, i);			
		
			//System.out.println("Node Name: "+o.Name(child));
			//System.out.println("Node Val.: "+o.Value(child));
			
			if (o.Type(child).compareToIgnoreCase("element") == 0) {
				// logically there will be more transition than location,
				// and more location than init | name | param => determined the order of conditions 
				if(o.Name(child).compareToIgnoreCase("transition") == 0) {
					/*System.out.println("Transition:");
					o.displayFrom(1,child); //*/
					//System.out.println("Extraction prop - Transition");
					transition = new Transition(child);
					if (transition.isGoodTransition() ) {
						transitions.add(transition);
						//System.out.println(transition);//*
					}
					else {System.out.println("Bad0");return false;}
				}
				else if(o.Name(child).compareToIgnoreCase("location") == 0) {
					/*System.out.println("State:");
					o.displayFrom(1,child); //*/
					//System.out.println("Extraction prop - State");
					state = new State(child);
					//System.err.println("GraphNode created is: "+state.toString());
					if (state.isGoodState() ) {
						states.add(state);
						//System.err.println("GraphNode added is: "+states.getLast().toString());
						//System.out.println(state.toString()); 
					}
					else {System.out.println("Bad1");return false;}					
				}
				else if(o.Name(child).compareToIgnoreCase("init") == 0) {
					//Extract the appropriate attribute
					//System.out.println("Extraction prop - init state");
					j=0 ;
					while( j < o.attributeCount(child)
							&& o.Name( (o.Attribute(child,j)) ).compareTo("ref") != 0) {j++;}
					if (j >= o.attributeCount(child) ) return false;
					//read the reference
					string = o.Value( o.Attribute(child,j) ); 
					//Set it type as initial
					state = findState(string, states);
					if (state != null ) { state.setInit();/*System.out.println(state.toString());*/}
					else {System.out.println("Bad2");return false;};
				}
				else if(o.Name(child).compareToIgnoreCase("name") == 0){
					//System.out.println("Extraction prop - name");
					if (o.childCount(child) != 1 ) {System.out.println("Bad4");return false;}
					propertyName = extractText(o.child(child,0)); 
					if (propertyName == null) {System.out.println("Bad5");return false;} 
					//System.out.println("Template: "+propertyName);
				}
				else if(o.Name(child).compareToIgnoreCase("parameter") == 0) {
					//System.out.println("Extraction prop - param");
					if (o.childCount(child) == 1 ) {
						parameters = o.extractParameters(child); 
						//list may be void but list should exist unless an error occured
						if (parameters == null) {System.out.println("Bad7");return false;}
					}	
				}
				else if(o.Name(child).compareToIgnoreCase("declaration") == 0) {
					//o.displayFrom(2,child);
					//System.out.println("Extraction prop - declaration");
					
					if (o.childCount(child) != 0 ) {
						LinkedList tmpList = o.extractDeclaration(child);
					
						if (tmpList == null) {System.out.println("Bad8");return false;}
						else {localVariables.addAll(tmpList);}
					}
				}
			}
			else {
					//System.out.println("Ignoring node:");
					//o.displayNodeInformation(1,child);
			} //Should be a text type that do not contain any information
			
		}
		
		return true;
	}
	protected Object clone()  throws CloneNotSupportedException
	{ 
		LinkedList list = new LinkedList();
		LinkedList states = new LinkedList();
		LinkedList transitions = new LinkedList();
		Iterator it;
	    State state;
	    Transition transition;
	    Variables var;
	    String string;
		Property copy = new Property();
		
		copy.succeeded = this.succeeded; 
		
		//System.err.println("Cloning property "+getPropClassName());
		
		//deep copy of nodes (compulsary for parameters renaming)
	    it=nodes.iterator();
	    while (it.hasNext()){
	    	state = (State)it.next(); 
	    	state = (State)state.clone();
	    	state.clear();
	    	
	    	states.add(state);
	    }
	    //copy.nodes = states;//*/
	    
	    //deep copy of edges (compulsary for parameter renaming, and synchro linkage with MethodProperty)
	    list = new LinkedList();
	    it=edges.iterator();
	    while (it.hasNext()){
	    	transition = (Transition)it.next(); 
	    	transition = (Transition)transition.clone();
	    	transition.clear();
	    	transitions.add(transition);
	    }
	    //copy.edges = transitions; 

	    //merging fresh states together with fresh transition
	    //using name matching
		Iterator it1, it2;
		State initial = null; 
		
		it1 = states.iterator() ;
		while (it1.hasNext()){
			state = (State)it1.next();
			if (state.isInitial() ) initial=state;

			it2 = transitions.iterator();
			while (it2.hasNext()){
				transition = (Transition)it2.next();			
				if (transition.from.compareTo(state.name)==0){
					transition.setIncommingNode(state);
					state.addAsOutgoingTransition(transition);
				}
				if (transition.to.compareTo(state.name)==0){
					transition.setOutgoingNode(state);
					state.addAsIncommingTransition(transition);
				}
			}
		}
		
		copy.clear();
		copy.addEdges(transitions);
		copy.addNodes(states);
		copy.setInitialNode(initial);   		
		
		
	    //deep copy of parameters
	    list = new LinkedList();
	    it=parameters.iterator();
	    while (it.hasNext()){
	    	var = (Variables)it.next(); 
	    	var = (Variables)var.clone();
	    	list.add(var);
	    }
	    
	    copy.parameters = list;
	    
	    copy.localVariables = this.localVariables ;
	    
	    return copy;
	}	
	private State modifyTransitionRef(LinkedList states, LinkedList transitions){
		//rename every state references in transition by its user defined state name
		// and make them point to each order in order to be able to build the graph structure inherited
		Iterator it1, it2;
		Transition transition;
		State state;
		State initial = null; 
		
		it1 = states.iterator() ;
		while (it1.hasNext()){
			state = (State)it1.next();
			if (state.isInitial() ) initial=state;

			it2 = transitions.iterator();
			while (it2.hasNext()){
				transition = (Transition)it2.next();			
				if (transition.from.compareTo(state.reference)==0){
					transition.from = state.name;
					transition.setIncommingNode(state);
					state.addAsOutgoingTransition(transition);
				}
				if (transition.to.compareTo(state.reference)==0){
					transition.to = state.name; 
					transition.setOutgoingNode(state);
					state.addAsIncommingTransition(transition);
				}
			}//normally, both 'from' and 'to' fields should have changed
			 //unless state hasn't been given a name
			
		}
		
		return initial;
	
	}
	private String extractText(Node text){
		Outils o = Outils.outilsFactory();
		String string = "";
		Matcher matcher;
		
		if ((o.Type(text).compareToIgnoreCase("text") ==0 ) ) 
		{
			string = o.Value(text);
			string.trim();
			matcher = Pattern.compile("(?s)(?m)^\\s*(\\S+.*)").matcher(string);
			if (matcher.find()){string=matcher.group(1);}
		}else return null;
		
		return string;
	}
	private State findState(String reference, LinkedList states) {
		State state;
		Iterator iter = states.iterator();
		while (iter.hasNext() ){ 
			state = (State)iter.next();
			if (reference.compareTo( state.reference) == 0) return state ;
		}
		return null;
	}


	/*
	 * public functions
	 * 
	 */
	
	public String synthesizeGlobalClass(LinkedList globalVariables, String globalPath){
		
		/*Synthesize the class representing the automaton
		reference should be shared by every method dealing with the current automaton */
		
		String string="";
		String tmp1;
		Iterator it;
		Variables var;

		string += "public class "+globalPath+" { \n";
		
		tmp1 = "";
		string += "\n\n\t//Insertion of the system static variables\n";
		it = globalVariables.iterator();
		if (it.hasNext())
		{
			do{
				var = (Variables)it.next();
				//TODO
				//DO not take annotation into consideration as it is local declaration
				if ((var.type.compareTo("broadcast chan")!= 0) && (var.type.compareTo("chan")!= 0)  ){
					//tmp1 += "\tpublic static /*@ pure @*/ "+var.getInterpretedType()+" "+var.name;
					//tmp1 +="() {return "+var.name+";}\n";
					string += "\t/*@ public static ghost "+var.getInterpretedType()+" "+var.name;
					if (var.initValue.compareTo("") != 0 ) { string += " = "+var.initValue+" ;"; }
					else string += " @*/ ;";
					string += " \n";
				}
			}while (it.hasNext());	
			string += tmp1 ;
		}
		else{string += "\t//(None to be added)\n";};
		
		string += getGlobalModifiers(globalPath);
		
		string += "\n\n}";
		return string;	
	}
	public String synthesizeAutomatonClass(LinkedList globalVariables, String globalPath){	
		
		String string="";
		string += "public class "+getPropClassName()+" { \n";		
		string += synthetizeClassVariables(globalVariables, globalPath);
		string += synthetiseClassModifiers(globalVariables, globalPath);
		string += "\n\n}";
		return string;	
	}
	public LinkedList synthesizeMethods(LinkedList globalVariables, String globalPath){

		/*Synthesize the annotation for every methods (instanceof MethodProperty) for the current property
		This function returns a list of MethodProperty, filled with the appropriate annotations 
		The list of globalVariable is compulsary to be able to generate the modifies clause*/
		
		LinkedList finalList;
		Iterator it ;	
		
		finalList = synthetiseMethodPropertyList(globalVariables, globalPath);
		return finalList;
	}
	public boolean renameParameters(LinkedList newParamList){

		/*Function renaming parameters, which is typically done at instanciation time 
	 	when parameters of the model are linked with global variables */
		
		Transition transition;
		State state;
		Iterator it1 ;
		Iterator it2 ;
		Iterator it3;
		Variables var1, var2 ;
		Matcher matcher ;
		int end;
		String tmp;

		it1 = newParamList.iterator();
		it2 = parameters.iterator();
		while (it1.hasNext() && it2.hasNext()){
			var1 = (Variables)it1.next();
			var2 = (Variables)it2.next();
			
			
			//matcher = Pattern.compile("(^|(.*\\W+))"+var2.name+"(\\W|$)").matcher("");//[^a-zA-Z0-9_]
			matcher = Pattern.compile("((^\\s*)|(.*\\W+))"+var2.name+"(\\W|$)").matcher("");
			
			
			//compare Parameters if identical, everything is fine
			//the elements of the new list and the older one are at obviously at the same place
			//as they are extracted by the 'same' method
			//Do not check type because it is not properly extracted
			// see : public LinkedList extractParameters(String string);
			if (var1.name.compareTo(var2.name)!=0){
				
				//System.err.println("renaming parameter "+var2.name+" to "+var1.name);
				
				//Update each transition
				it3 = edges.iterator();
				while(it3.hasNext()){
					transition=(Transition)it3.next();
					
					//modify guard					
					tmp = new String(transition.guard);
					matcher.reset(tmp);
					while (matcher.find()) {						
						tmp = matcher.group(1)+var1.name;
						if ((transition.guard.length()-matcher.end())>0) {tmp += transition.guard.substring(matcher.end()-1);}						
						matcher.reset(tmp);
					} 
					transition.guard = tmp;
					
					//modify synchro
					tmp = new String(transition.synchro);
					matcher.reset(tmp);
					while (matcher.find()) {
						tmp = matcher.group(1)+var1.name;
						if ((transition.synchro.length()-matcher.end())>0) {tmp += transition.synchro.substring(matcher.end()-1);}
						matcher.reset(tmp);
					} 
					transition.synchro = tmp;
					
					//modidfy update
					tmp = transition.update;
					matcher.reset(tmp);
					while (matcher.find()) {
						tmp = matcher.group(2)+" "+var1.name;
						if ((transition.update.length()-matcher.end())>0) {tmp += transition.update.substring(matcher.end()-1);}
						matcher.reset(tmp);
					}		
					transition.update = tmp; 
				}
				
				//modify the invariant of state if necessary
				it3 = nodes.iterator();
				while(it3.hasNext()){
					state=(State)it3.next();
					//modify guard
					tmp = state.invariant;
					matcher.reset(tmp);
					while (matcher.find()) {
						tmp = matcher.group(2)+" "+var1.name;
						if ((state.invariant.length()-matcher.end())>0) {tmp += state.invariant.substring(matcher.end()-1);}
						matcher.reset(tmp);
					} 
					state.invariant = tmp;
				}
			}
			//else nothing to be changed	
			
		}
		if (it1.hasNext() || it2.hasNext()) return false; //mismatch, list are not the same length
		
		return true; // turn it to true when design complited
	}
	
	
	/* Functions inherent to implements clause */
	public int compareTo(Object obj){
		
			int i;
			Property prop2;
			
			if(!(obj instanceof Property)) throw new ClassCastException();
			prop2=(Property)obj;
			i = this.propertyName.compareTo(prop2.propertyName);
						
			return i;
	}
	


	/* Synthesis private function */
	
	private String synthetizeClassVariables(LinkedList globalVariables, String globalPath){
		
		int i;
		String string = "" ;
		String stateName="";
		String tmp1;
		String invariants = "", invariant2 = "";
		Iterator it1 ;
		State state;
		Variables var;
		
		
		//insert local variables 
		string += "\n\n\t//Local variables\n";
		tmp1 = "";
		it1=localVariables.iterator();
		if (it1.hasNext())
		{
			do{
				var = (Variables)it1.next();
				//TODO
				//DO not take annotation into consideration as it is local declaration
				if ((var.type.compareTo("broadcast chan")!= 0) && (var.type.compareTo("chan")!= 0)  ){
					//tmp1 += "\tpublic static /*@ pure @*/ "+var.getInterpretedType()+" "+var.name;
					//tmp1 +="() {return "+var.name+";}\n";
					string += "\t/*@ private static ghost "+var.getInterpretedType()+" "+var.name; //cf:  http://java.about.com/od/beginningjava/l/aa_file_struct.htm
					if (var.initValue.compareTo("") != 0 ) { string += " = "+var.initValue; }
					string += "; @*/ \n";
				}else System.err.println ("Channel "+var.name+" should not be local (Ignored by synthesis)");
			}while (it1.hasNext());	
			string += tmp1;
		}
		else{string += "\t//(None to be added)\n";};
		
		
		
		//insert nodes definition
		string += "\n\n\t//State Definition\n";
		stateName = getStateFieldName();//propertyName+"State";
		tmp1 = "\t/*@ public static int "+stateName+" = ";
		i = 0 ;
		it1 = nodes.iterator();
		while (it1.hasNext()){
			state= (State)it1.next();
			string += "\t/*@ public final static ghost int "+state.name+" = "+i+" ; @*/ \n"; 
			if (state.isInitial()) tmp1 +=state.name+" ; @*/ \n";
			//TODO invariant would surely need to be interpreted or splitted to several invariants
			if (state.invariant.compareTo("")!=0){ 
				invariants += "\t//@ static invariant ("+stateName+"=="+state.name+") ==> (";
				invariants += addLocalPath(addGlobalPath(globalVariables,globalPath,state.invariant))+") ; \n";
			}
			invariant2 += "\t              "+stateName+"=="+state.name+" || \n";
			i++;
		}
		string += tmp1 + "\n\t//nodes invariants\n";
		i = invariant2.lastIndexOf('|');
		invariant2 = "\t/*@ static invariant ("+invariant2.substring(15, i-2)+" ); \n\t@*/ \n";
		
				
		//insert invariants of the property
		string += invariant2; //describes possible nodes of the automaton
		string += invariants; //contains all the nodes invariants
		
		//string += synthetizeFucntions();
		
		return string;	
	
	}
	private String synthetiseClassModifiers(LinkedList globalVariables, String globalPath){
		
		/**
		 * This function is responsible for generating all the modification function
		 * 		associated with each implemented property. It more specifically generate
		 * 		the modification function of the state (pure) and the update function of
		 * 		of all the variable introduced for the need of the description. Besides,
		 * 		it also sets the information conserning the global variables used by the
		 * 		getGlobalModifiers function after all the properties have been synthesized.
		 **/
		
		
		
		/* Variables Definition
		{//Strings used for the "goNext()" function */
			String methodReferences;
			String goNextEnsures= "";
			String goNextElseAnnotation = ""; 	//contains the conditions for keeping state untouched
			String goNextBody = "";
			
			//Variables used for local variables modifications
			Iterator it, it1, it2, it3, it4, it5 ;			
			LinkedList varNameList		= new LinkedList();
			LinkedList annotationList	= new LinkedList();
			LinkedList elseAnnotationList = new LinkedList();
			LinkedList updateMethodList	= new LinkedList();
		
			//Varible used for generating output strings
			String string="", cond, prefixedCond, tmp="", tmp2 = "", indent1="\t\t", indent2="\t\t\t", indent3="\t\t\t\t";
			int k;
			LinkedList prefixedGlobalVariables = new LinkedList();
			LinkedList mpList = new LinkedList();
			LinkedList localModifiedVar ;
			LinkedList globalModifiedVar ;
			LinkedList methodNameList = new LinkedList();
			Variables var = new Variables();
			Transition transition, tmpTransition; /*
		} */
		
			
		/* Initialization */
		String state = "state";
		String methodId = "methodAction";
		String prefix = getPropClassName();
		string += "\n\n\t/*	Modification function of the Automaton   */\n";
		{//Building the prefixedGlobalVariable list
			it2 = globalVariables.iterator();
			while (it2.hasNext()){
				var = (Variables)it2.next();
				try{ var = (Variables) var.clone();}
				catch(Exception e){ 
					System.err.println("Variables.clone() failed, resulting in potentially corrupted prefix for global Variables");}
				var.name = globalPath+"."+var.name;
				prefixedGlobalVariables.add(var);
			}
		}
		
		/* Building Modifiers and their associated annotations */
		Collections.sort(edges); //sort using first the 'from' field
		it =  edges.iterator();
		while (it.hasNext()){
			//for each transition
			transition = (Transition) it.next();
			
			
			//add information about global variable and their modification
			{	
				try {tmpTransition = (Transition) transition.clone();}
				catch(Exception e){ 
					tmpTransition = transition; 
					System.err.println("Transition.clone() failed, resulting in potentially corrupted prefix");}
				mpList.add(tmpTransition.mp);
				
				//add local path to updates
				tmpTransition.guard = addLocalPath(tmpTransition.guard);
				tmpTransition.update = addLocalPath(tmpTransition.update);
				
				//affectation of the state to modifiable and propertyList if not already there
				globalModifiedVar = new LinkedList();
				globalModifiedVar.addAll(getModifiedVariables(globalVariables,tmpTransition.update));	
					
				//build the general condition for modification
				prefixedCond = methodId+"=="+prefix+"."+getMethodActionName(tmpTransition); 
				prefixedCond += " && "+prefix+"."+state+"=="+prefix+"."+tmpTransition.from;
				if (tmpTransition.guard.compareTo("true")!=0 || tmpTransition.guard.compareTo("")!=0)
					prefixedCond += " && "+tmpTransition.guard;
				
				//add effectively
				//System.err.println("Call General var for property: "+getPropClassName());
				addToGlobalModifiers(transition,globalModifiedVar,prefixedCond,state,methodId);
			}//*/
				
			//Prepare all variables: build the prefixed version of the transition, get the modified variables
			{ 
				try {tmpTransition = (Transition) transition.clone();}
				catch(Exception e){ 
					tmpTransition = transition; 
					System.err.println("Transition.clone() failed, resulting in potentially corrupted prefix");}
				mpList.add(tmpTransition.mp);	
				
				//add path to the global variables			
				tmpTransition.guard =  addPath(globalVariables, globalPath, tmpTransition.guard);
				tmpTransition.update = addPath(globalVariables, globalPath, tmpTransition.update);
				
				//build the general condition for modification
				prefixedCond = methodId+"=="+prefix+"."+getMethodActionName(tmpTransition); 
				prefixedCond += " && "+prefix+"."+state+"=="+prefix+"."+tmpTransition.from;
				if (tmpTransition.guard.compareTo("true")!=0 || tmpTransition.guard.compareTo("")!=0)
					prefixedCond += " && "+tmpTransition.guard; 
				
				//add path to the global variables			
				//tmpTransition.guard =  addGlobalPath(globalVariables, globalPath, transition.guard);
				//tmpTransition.update = addGlobalPath(globalVariables, globalPath, transition.update);
			
				//affectation of the state to modifiable and propertyList if not already there
				localModifiedVar = new LinkedList();
				localModifiedVar.addAll(getModifiedVariables(localVariables, tmpTransition.update));
				System.err.println("----------------------"+tmpTransition.update+" : "+localModifiedVar+"-----------");
				
				
				//build the general condition for modification
				cond = methodId+"=="+getMethodActionName(tmpTransition); 
				//cond += " && "+state+"=="+tmpTransition.from;
				if (tmpTransition.guard.compareTo("true")!=0 || tmpTransition.guard.compareTo("")!=0)
					cond += " && "+tmpTransition.guard;
			}
			

			//Add information to goNext() method, which is the "state" field modifier 
			{
				//annotation
				goNextEnsures += indent1+"(("+prefixedCond+") ==> \\result=="+tmpTransition.to+") && \n";
				goNextElseAnnotation += indent2+"!("+prefixedCond+") && \n";
				
				//body (works because transition were sorted using from fields)
				/*if (tmp.compareTo(tmpTransition.from)!=0) {
					goNextBody += indent2+"break;\n";
					goNextBody += indent1+"case "+tmpTransition.from+":\n";
					tmp = tmpTransition.from;
				}
				goNextBody += indent2+"if ("+cond+") \n"+indent3+"return "+tmpTransition.to+";\n";*/
				
			}
		
		
			//Add information in Local variables modifiers
			{
				boolean found ;
				Matcher matcher;
				Variables searchedVar;
				String updateAffectation;
				String currentVarName;
				String currentAnnotations;
				String currentFunctionBody;
				String currentElseAnnotation;
				int i;
				String[] updateExpressions = tmpTransition.getInterpretedUpdate().split(" , ");
				
				it1 = localModifiedVar.iterator();
				//for each variable modified by the transition
				while (it1.hasNext()){
					searchedVar = (Variables) it1.next();
					
					System.err.println("searching for update expression of variable "+searchedVar.name);
					
					//search if this variable is already in the list 
					//the four following list are ordered so that the ith element of the first list
					//  is related to the ith of the other lists.
					it2 = varNameList.iterator();
					it3 = annotationList.iterator();
					it4 = updateMethodList.iterator() ;
					it5 = elseAnnotationList.iterator();
					
					found = false;
					i = 0;
					while (it2.hasNext() && !found){
						currentVarName = (String) it2.next();
						currentAnnotations = (String) it3.next();
						currentFunctionBody= (String) it4.next();
						currentElseAnnotation = (String) it5.next();
						if (currentVarName.compareTo(searchedVar.name) == 0){ found = true ;}
						else {i++;}
					}
					if (found==false) {
						//first time the variable is encountered in update field
						currentVarName = searchedVar.name;
						//method could have been pure as well in which case entry/exit action have been different
						currentAnnotations = "\t//@ modifies "+searchedVar.name/*+"\\nothing"*/+"; \n";
						currentFunctionBody = "\t public static void"/*+searchedVar.getInterpretedType()*/;
						currentFunctionBody+= " "+getUpdateFunctionDeclaration(searchedVar.name, methodId);
						currentElseAnnotation = "";
					}
					else {
						found = false;
						//temporary removal : see later on
						currentVarName = (String) varNameList.remove(i);
						currentAnnotations  =   (String) annotationList.remove(i);					
						currentFunctionBody =   (String) updateMethodList.remove(i);
						currentElseAnnotation = (String) elseAnnotationList.remove(i);
					}
					
					//Add information effectively
					i=0 ;
					while ( (i<updateExpressions.length) && (found==false)){
						matcher = Pattern.compile("(^|\\W)"+searchedVar.name+"\\s*=.*").matcher(updateExpressions[i]);
						if (matcher.find()) found = true;
						i++;
					}
					if (found == true){
						//isolation of the update expression
						updateAffectation = updateExpressions[i-1].substring(updateExpressions[i-1].indexOf("=")+1) ;
						updateAffectation.trim();
						//remove annotations
						updateAffectation = updateAffectation.replaceAll("^(.*)//@.*$" , "$1");
						updateAffectation = updateAffectation.replaceAll("(?m)(?s)^(.*)/\\*.*?\\*/(.*)", "$1\n$2");
						updateAffectation = updateAffectation.trim();
						
						currentAnnotations   += "\t/*@ ensures ("+prefixedCond+") ==> "+searchedVar.name+"== \\old("+/*addLocalPath(**/updateAffectation/*)*/+") @*/;\n";
						//currentFunctionBody  += indent1+"if ("+cond+" && "+state+"=="+tmpTransition.from+") {\n"+indent2+searchedVar.name+"="+updateAffectation+"; return; } \n";
						currentElseAnnotation+= indent1+"!("+prefixedCond+") && \n";
					
					}else System.err.println("Update expression not found for variable: "+searchedVar.name);
					
					varNameList.add(searchedVar.name);
					annotationList.add(currentAnnotations);					
					updateMethodList.add(currentFunctionBody);
					elseAnnotationList.add(currentElseAnnotation);
					
				}
			}
			
													
			/*Build here the method Reference*/
			methodNameList.add(tmpTransition.mp.getMethodName());
		
			
		}

		tmp2 = "";
		k = 0;
		Collections.sort(methodNameList);
		it = methodNameList.iterator();
		while (it.hasNext()){
			tmp = (String) it.next();
			if (tmp.compareTo(tmp2) != 0 ){
				string += "\t /*@ public final static ghost int "+getMethodActionName(tmp, "Call")+" = "+k+"; @*/ \n" ; k++; 
				string += "\t /*@ public final static ghost int "+getMethodActionName(tmp, "Normal Terminaison")+" = "+k+"; @*/ \n" ; k++; 
				string += "\t /*@ public final static ghost int "+getMethodActionName(tmp, "Except Terminaison")+" = "+k+"; @*/ \n" ; k++; 
				tmp2 = tmp;
			}
		}
		
		
		/* finalise goNext() stuff */
		//goNextBody = goNextBody.substring(goNextBody.indexOf("\n")); //remove the first break !
		goNextBody = "\tpublic static /*@pure@*/ int goNext(int "+methodId+");";//"){\n"+indent1+"switch("+state+"){\n"+goNextBody;
		//goNextBody += indent3+"break;\n"+indent2+"default : break;\n"+indent1+"}\n"+indent1+"return "+state+";\n\t}\n";
		goNextEnsures = "\t/*@ ensures "+goNextEnsures.substring(indent1.length(),goNextEnsures.length()-4)+" ; @*/ \n";
		goNextEnsures = "\t//@ modifies \\nothing ; \n"+goNextEnsures;
		goNextElseAnnotation = "\t/*@ ensures ("+goNextElseAnnotation.substring(indent2.length(),goNextElseAnnotation.length()-4);
		goNextElseAnnotation+= ") ==> \\result=="+state+" ; @*/ \n";
		
		/* add goNext() to output */
		string += "\n\n"+goNextEnsures;
		string += goNextElseAnnotation;
		string += goNextBody;
		
		/* finalise Local update functions and add them to the ouput*/
		string += getVarModifiers("", varNameList, 
				updateMethodList, annotationList, elseAnnotationList);
		
		
		return string ;
	}
	private void addToGlobalModifiers(Transition tmpTransition, LinkedList globalModifiedVar, String prefixedCond,
			String state, String methodId){
		//Add information in Global variables modifiers
		
		String string = "", indent1="\t\t", indent2="\t\t\t", indent3="\t\t\t\t";
		Iterator it1, it2, it3, it4, it5;
		
		boolean found ;
		Matcher matcher;
		Variables searchedVar;
		String updateAffectation;
		String currentVarName;
		String currentAnnotations;
		String currentFunctionBody;
		String currentElseAnnotation;
		
		int i;
		String[] updateExpressions = tmpTransition.getInterpretedUpdate().split(" , ");
		
		it1 = globalModifiedVar.iterator();
		//for each variable modified by the transition
		while (it1.hasNext()){
			searchedVar = (Variables) it1.next();
			//System.err.println("Serching for: "+searchedVar.name);
			//search if this variable is already in the list 
			it2 = ModifiedListGlobalVar.iterator();
			it3 = updateMethodannotationList.iterator();
			it4 = updateMethodListGlobalVar.iterator() ;
			it5 = updateMethodelseAnnotationList.iterator();
			found = false;
			i = 0;
			while (it2.hasNext() && !found){
				currentVarName = (String) it2.next();
				currentAnnotations = (String) it3.next();
				currentFunctionBody= (String) it4.next();
				currentElseAnnotation = (String) it5.next();
				if (currentVarName.compareTo(searchedVar.name) == 0){ found = true ;}
				else {i++;}
			}
			if (found==false) {
				currentVarName = searchedVar.name;
				currentAnnotations = "\t//@ modifies "+searchedVar.name+"; \n";
				currentFunctionBody = "\t public static void "/*+searchedVar.getInterpretedType()*/;
				currentFunctionBody+= " "+searchedVar.name+"(int "+methodId+");";//){ \n";
				currentElseAnnotation = "";
			}
			else {
				found = false;
				currentVarName = (String) ModifiedListGlobalVar.remove(i);
				currentAnnotations  =   (String) updateMethodannotationList.remove(i);					
				currentFunctionBody =   (String) updateMethodListGlobalVar.remove(i);
				currentElseAnnotation = (String) updateMethodelseAnnotationList.remove(i);
			}
			
			//Add information effectively
			i=0 ;
			while ( (i<updateExpressions.length) && (found==false)){
				matcher = Pattern.compile("(^|\\W)"+searchedVar.name+"\\s*=.*").matcher(updateExpressions[i]);
				if (matcher.find()) found = true;
				i++;
			}
			if (found == true){
				
				//System.err.println("Adding update: "+updateExpressions[i-1]+" ( from property: "+getPropClassName()+")");
				
				//isolation of the update expression
				updateAffectation = updateExpressions[i-1].substring(updateExpressions[i-1].indexOf("=")+1) ;
				updateAffectation.trim();
				//remove annotations
				updateAffectation = updateAffectation.replaceAll("^(.*)//@.*$" , "$1");
				updateAffectation = updateAffectation.replaceAll("(?m)(?s)^(.*)/\\*.*?\\*/(.*)", "$1\n$2");
				updateAffectation = updateAffectation.trim();
				
				currentAnnotations   += "\t/*@ ensures ("+prefixedCond+") ==> "+searchedVar.name+" == \\old("+updateAffectation+") @*/;\n";
				//currentFunctionBody  += indent1+"if ("+prefixedCond+") { \n"+indent2+searchedVar.name+"="+updateAffectation+"; return; } \n";
				currentElseAnnotation+= indent1+"!("+prefixedCond+") && \n";
				
				System.err.println();
				
			}//else System.err.println("Update expression not found for variable: "+searchedVar.name);
			
			ModifiedListGlobalVar.add(searchedVar.name);
			updateMethodannotationList.add(currentAnnotations);					
			updateMethodListGlobalVar.add(currentFunctionBody);
			updateMethodelseAnnotationList.add(currentElseAnnotation);
		
		}
	}
	private String getGlobalModifiers(String globalPath){
		
		String string = "";

		string = getVarModifiers("",
					ModifiedListGlobalVar,
					updateMethodListGlobalVar,
					updateMethodannotationList,
					updateMethodelseAnnotationList);
		
		return string;
	
	}
	private String getVarModifiers(String accessor, LinkedList varNameList, 
			LinkedList updateMethodList, LinkedList annotationList, LinkedList elseAnnotationList){
		 
		String string = "", indent1="\t\t", indent2="\t\t\t", indent3="\t\t\t\t";
		Iterator it1, it2, it3, it4; 
	
		/* finalise Local update functions and add them to the ouput*/
		
		String firstVarName;
		String currentVarName;
		String currentFunctionBody;
		String currentElseAnnotation;
		
		it1 = varNameList.iterator();
		if (it1.hasNext()){
			
			firstVarName = (String) varNameList.getFirst();
			//For each variables
			do{
				//remove strings
				currentVarName 	= (String) varNameList.removeFirst();
				currentFunctionBody	= (String) updateMethodList.removeFirst();
				currentElseAnnotation=(String) elseAnnotationList.removeFirst();
				//modify strings
				//currentFunctionBody += indent1+"else return "+/*currentVarName+*/"; \n\t}\n";
				currentElseAnnotation = "\t/*@ ensures (\n"+currentElseAnnotation.substring(0,currentElseAnnotation.length()-4)+") " ;	
				//add modified strings
				varNameList.addLast(currentVarName);
				updateMethodList.addLast(currentFunctionBody);
				elseAnnotationList.addLast(currentElseAnnotation);
			}while ( ((String)varNameList.getFirst()).compareTo(firstVarName) !=0 );
		}
		it1 = varNameList.iterator(); //because list could have been modified in the mean time => but throws a ConcurrentModificationException ??
		it2 = annotationList.iterator();
		it3 = elseAnnotationList.iterator();
		it4 = updateMethodList.iterator();
		while(it1.hasNext()){
			string += "\n\n\t//";
			firstVarName = (String) it1.next();
			string += firstVarName;
			string += "\n";
			string += (String) it2.next();
			string += (String) it3.next();
			if (accessor.compareTo("")==0){
				string += "==> "+firstVarName+"==\\old("+firstVarName+"); @*/ \n";
			}else {
				string += "==> "+accessor+"."+firstVarName+"== \\old("+addAccessor(accessor,firstVarName)+") ; @*/ \n";
			}
			string += (String) it4.next();
		}
		
		return string;
	}

	
	private LinkedList synthetiseMethodPropertyList(LinkedList globalVariables, String globalPath){
		
			/* Algo
			 	

			*/

			int i,j;
			boolean found;
			Iterator it;
			LinkedList finalList = new LinkedList();
			LinkedList mpList = new LinkedList();
			LinkedList outTransitionList, inTransitionList;
			LinkedList possiblePaths;
			LinkedList modifiedVariableList;
			LinkedList prefixedGlobalVariables = new LinkedList();
			LinkedList prefixedLocalVariables  = new LinkedList();
			LinkedList updateList;
			Transition inTransition, outTransition, tmpTransition;
			Variables var;
			String[] entryUpdateParam = new String[1];
			String[] exitUpdateParam = new String[1];
			MethodProperty mp, mp2;
			
			//Building Prefixed Variable list
			it = globalVariables.iterator();
			while (it.hasNext()){
				var = (Variables)it.next();
				try{ var = (Variables) var.clone();}
				catch(Exception e){ 
					System.err.println("Variables.clone() failed, resulting in potentially corrupted prefix for global Variables");}
				var.name = globalPath+"."+var.name;
				prefixedGlobalVariables.add(var);
			}
			
			it = localVariables.iterator();
			while (it.hasNext()){
				var = (Variables)it.next();
				try{ var = (Variables) var.clone();}
				catch(Exception e){ 
					System.err.println("Variables.clone() failed, resulting in potentially corrupted prefix for global Variables");}
				var.name = getPropClassName()+"."+var.name;
				prefixedLocalVariables.add(var);
			}
			
			
			//Building list
			inTransitionList = new LinkedList();
			outTransitionList= new LinkedList();
			i = edges.size();
			while(i>0){
				inTransition = (Transition) edges.get(i-1);
				if ( inTransition.synchroTypeToString().compareTo("Call")==0 ) inTransitionList.add(inTransition);
				else outTransitionList.add(inTransition);
				i--;
			}
			
			//System.err.println("Sorting Call and Return Transition resulted in: ");
			//System.err.println(inTransitionList+"\n\n\n");
			//System.err.println(outTransitionList);
			//System.err.println("Beginning synthesis of method used in "+getPropClassName());
			
			//Build MethodProperty for every method call to possible return
			Collections.sort(outTransitionList);
			var =  new Variables();
			i=inTransitionList.size();
			while(i>0){
				//for every call to this method
				inTransition = (Transition) inTransitionList.get(i-1);
				entryUpdateParam[0] = getPropClassName()+"."+getMethodActionName(inTransition);
				
				j=outTransitionList.size();
				while(j>0){
					outTransition = (Transition) outTransitionList.get(j-1);
					if (outTransition.mp.getMethodName().compareTo(inTransition.mp.getMethodName())==0) {
						
						exitUpdateParam[0] = getPropClassName()+"."+getMethodActionName(outTransition);
						
						//System.err.println("Operating on the following \"return\" transition: "+outTransition);
											
						//Evaluate the possible outputPoints
						System.err.println("start with "+inTransition);
						System.err.println("end with "+outTransition);
						
						//get all possible paths
						possiblePaths=compatiblePath(inTransition, outTransition, inTransition.mp);
						System.err.println(" => there are "+possiblePaths.size()+" possible path(s)" );
						
						for(int n=possiblePaths.size() ; n>0 ; n--){
							
							//preparation phase
							mp = inTransition.mp; // outTransition is obviously the same her
							try {tmpTransition = (Transition) outTransition.clone();}
							catch(Exception e){ 
								tmpTransition = outTransition; 
								System.err.println("Transition.clone() failed, resulting in potentially corrupted prefix");
							}
							
							tmpTransition.guard = addPath(globalVariables, globalPath, tmpTransition.guard);
							tmpTransition.guard = addPath(localVariables, getPropClassName(),tmpTransition.guard);
							tmpTransition.update= addPath(globalVariables, globalPath, tmpTransition.update);
							tmpTransition.update= addPath(localVariables, getPropClassName(),tmpTransition.update);
							modifiedVariableList = getModifiedVariables(prefixedGlobalVariables,tmpTransition.update);
							modifiedVariableList.addAll(getModifiedVariables(prefixedLocalVariables ,tmpTransition.update));
							
											
							//System.err.println("---------------------------\n"+tmpTransition.update+"\n---------");							
							
							updateList = new LinkedList();
							for (int k=modifiedVariableList.size() ; k>0 ; k--) 
								updateList.add(getPropClassName()+"."+getUpdateFunctionName(((Variables)modifiedVariableList.get(k-1)).name));
							
							//affectation to the MethodProperty
							mp.addModifies(modifiedVariableList);
							
							
							if (outTransition.synchroTypeToString().compareTo("Normal Terminaison")==0){
								mp.addNormalPostcond(getStateFieldName(),getPropClassName(), inTransition, tmpTransition);
								for(int k=updateList.size()-1 ; k>=0 ; k--) mp.addNormalExitActions((String)updateList.get(k), exitUpdateParam);
							}else{
								mp.addExceptPostcond(getStateFieldName(),getPropClassName(), inTransition, tmpTransition);
								for(int k=updateList.size()-1 ; k>=0 ; k--)mp.addExceptExitActions((String)updateList.get(k), exitUpdateParam);
							}
						}
						
						
					}
					else {/*System.err.println("Following Transition is not associated to the right method: "+outTransition);*/}
					j--;
				}
				//all possible terminaison have been treated (if any) for the given 
				try {tmpTransition = (Transition) inTransition.clone();}
				catch(Exception e){ 
					tmpTransition = inTransition; 
					System.err.println("Transition.clone() failed, resulting in potentially corrupted prefix");
				}
				mp = inTransition.mp;
				mpList.add(mp);
				tmpTransition.guard = addPath(globalVariables, globalPath, tmpTransition.guard);
				tmpTransition.guard = addPath(localVariables, getPropClassName(),tmpTransition.guard);
				tmpTransition.update = addPath(globalVariables, globalPath, tmpTransition.update);
				tmpTransition.update = addPath(localVariables, getPropClassName(),tmpTransition.update);
				modifiedVariableList = getModifiedVariables(prefixedGlobalVariables,tmpTransition.update);
				modifiedVariableList.addAll(getModifiedVariables(prefixedLocalVariables ,tmpTransition.update));

				
				updateList = new LinkedList();
				for (int k=modifiedVariableList.size() ; k>0 ; k--) {
					updateList.add(getPropClassName()+"."+getUpdateFunctionName(((Variables)modifiedVariableList.get(k-1)).name));
					System.err.println("Modifying variable: "+((Variables)modifiedVariableList.get(k-1)).name);
				}
				
				//affectation to the MethodProperty
				mp.addPrecond(getStateFieldName(),getPropClassName(), tmpTransition);
				for(int k=updateList.size()-1 ; k>=0 ; k--) mp.addEntryActions((String)updateList.get(k), entryUpdateParam);
				mp.addModifies(modifiedVariableList);
				
				
				//System.err.println("current call transition is: "+i);
				i--;
			}
			
			
			//remove duplicate entry in mpList
			mp = new MethodProperty("",""); 
			Collections.sort(mpList);
			it = mpList.iterator();
			while (it.hasNext()){
				mp2 = mp;
				mp = (MethodProperty) it.next(); 
				
				if (mp.compareTo(mp2)!= 0 ){finalList.add(mp);}
			}
			
			Outils o = Outils.outilsFactory();
			String[] exitUpdateParamExcep = new String[1];
			it = finalList.iterator();
			while (it.hasNext()){
				mp = (MethodProperty) it.next(); 
				entryUpdateParam[0]     = getPropClassName()+"."+getMethodActionName(mp.getMethodName(), "Call");
				exitUpdateParam[0]      = getPropClassName()+"."+getMethodActionName(mp.getMethodName(), "Normal Terminaison");
				exitUpdateParamExcep[0] = getPropClassName()+"."+getMethodActionName(mp.getMethodName(), "Except Terminaison");
				
				mp.releaseAutomaton(getPropClassName(),getStateFieldName(), "goNext",
						entryUpdateParam,
						exitUpdateParam ,
						exitUpdateParamExcep); //inUpdateParam can be used also	
			}
					
			return finalList;
			
		}

	
	/* Exploration functions*/
	private LinkedList compatiblePath(Transition inTransition,Transition outTransition, MethodProperty mp){
		
		/* Returns weather or not a compatible path has been found to link transitionCall to 
		 		its associated terminaison */
			
		
		/*	Algo
		 	
		 	 - get all simple path
		 	 - get all simple circuit
		 	 
		 	 - for each path of the list of simple path 
		 	 		- search for compatibility of depth along the path
		 	 		- if compatible add to pathList
		 	 		- for each circuits 
		 	 				- if circuit compatible (make/maintain compatibility)
		 	 					add to pathList

			- return pathList

		*/
		
		//System.err.println("Enter compatible path method ("+getPropClassName()+")");
		
		GraphNode start = inTransition.getOutgoingNode();
		GraphNode end = outTransition.getIncommingNode();
		
		SimplePath path;
		SimpleCircuit circuit;
		LinkedList pathList = new LinkedList();
		LinkedList simplePaths = super.findAllSimplePath(start,end);
		LinkedList simpleCircuits = super.findAllSimpleCircuit();
		GraphNode connectState, tmpState;
		LinkedList tmpPath;
		LinkedList subPath;
		boolean test;
		int compatibility ;
		int circuitCompatibility; 
		int i,j,k,m;
		
		 
		//path can be void iff start and end are equal, otherwise no path has been found
		if (simplePaths.size()==0 && (start.compareTo(end)!=0)) return pathList;
		
		for(i= simplePaths.size() ; i>0 ; i--){
			path = (SimplePath) simplePaths.get(i-1);
			path.addHead(inTransition);
			path.addQueue(outTransition);
					
			//System.err.println("analysing simple path: "+path);
									
			if (isPotentialPath(path.getPath(), mp)) {	
				//find if path can be compatible interms of path
				compatibility = callDepthForPath(path.getPath(), mp);
				if (compatibility==0) pathList.add(path.getPath());	
			
				for(j=simpleCircuits.size() ; j>0 ; j--){
					circuit = (SimpleCircuit) simpleCircuits.get(j-1);
					System.err.println("evaluatin circuit n"+j);
					circuitCompatibility = callDepthForPath(circuit.getPath(), mp);
					System.err.println("compatibility is="+circuitCompatibility);
					
					//find the circuit can be compatible in terms of depth
					connectState = (GraphNode) circuit.findInnerConnectionWith(path);
					if (circuit.contains(connectState) 
							&& !circuit.contains(inTransition) && !circuit.contains(outTransition) ) //TODO : VERY STRONG RESTRICTION
					{
						System.err.println("Circuit connects to path");
						//Count the number of time the circuit should be taken
						test = false; k=0;
						if (compatibility>0 && circuitCompatibility<0){
							while ((k*circuitCompatibility+compatibility)>0) k++;
							test = true;
						}
						else if (compatibility<0 && circuitCompatibility>0){
							while ((k*circuitCompatibility+compatibility)<0) k++;
							test = true;
						}
						else if (compatibility==0 && circuitCompatibility==0) test=true;
						
						
						//Build path if a solution was found	
						if ((k*circuitCompatibility+compatibility)==0 && test) {
							//create first part of the path
							LinkedList newPath = new  LinkedList();
							m=0;
							do {
								newPath.add(path.getPath().get(m));
								tmpState = ((OrientedEdge)path.getPath().get(m)).getOutgoingNode();
								m++;
							}while (m<path.size() && connectState.compareTo(tmpState)!=0);
	
							// if circuitCompatibility = 0 add only once
							if (k==0) {k=1;}
							//add circuit the adequate number of time
							for ( ; k>0 ; k--) {newPath.addAll(circuit.getPath());}
							//add last part of the path
							while (m<path.size()){newPath.add(path.getPath().get(m)); m++;}
							
							//if compatible no only in terms of Depth (avoid multiple return to zero)
							if (isPotentialPath(newPath,mp)) pathList.add(newPath);
							
						}
					}
				}
			}
		
		}
		
		//System.err.println("returning path list (from methode compatiblePath)");
		return pathList;	
			
	}
	private boolean isPotentialPath(LinkedList transitions, MethodProperty mp){
		/*	Tell if the path propose by the succession of transition may compatible 
		 * 		or not. If false is return, the path followed is not compatible (never
		 * 		mind the depth returned by call for depth). If true is returned, then 
		 * 		the path may well be compatible (some transition might be necessary to 
		 * 		make it a real compatible path).
		 * 
		 * 	The discriminating factor is the multiple return to 0. the first return to 0 
		 * 		notifies that the function we target (designated by mp) is terminating. Thus
		 * 		all future variation of the depth (count) is not anymore significant.
		 * 
		 * 		ie :  	Call -> Call -> return -> return -> ... >> isPotentialPath
		 * 				Call -> return -> Call -> return -> ... >> !isPotentialPath
		 * 				Call -> Call ->  ....  -> return   		>> isPotentialPath
		 */
		
		Transition transition;
		int count = 0 ;
		boolean noMoreChangeAllowed = false;
		boolean valid = true;
		int j = transitions.size();
		for(int i=0 ; i<j ; i++){
			transition = (Transition) transitions.get(i);
			if (transition.mp.compareTo(mp)==0){
				if (noMoreChangeAllowed == true) return false;
				if (transition.synchroTypeToString().compareTo("Call")==0) count ++;
				else count --; /* "Normal Terminaison" || "Except Terminaison" */			
				if (count==0) noMoreChangeAllowed = true;
			}
		}
				
		return valid;
	}
	private int callDepthForPath(LinkedList transitions, MethodProperty mp ){
		/* returns the number of function (associated to a given mp) still in activity
		 * 		at the end of the path 
		 * 		(eg.: 	if 2 return are missing function will return 2 
		 * 				if a call is missing function will return -1)
		 */
		
		Transition transition;
		int count = 0 ;
		
		for(int i=transitions.size() ; i>0 ; i--){
			transition = (Transition) transitions.get(i-1);
			if (transition.mp.compareTo(mp)==0){
				if (transition.synchroTypeToString().compareTo("Call")==0) count ++;
				else count --; /* "Normal Terminaison" || "Except Terminaison" */			
			}
		}
				
		return count;
	}
	private boolean connectionCircuitToPath(SimpleCircuit circuit, SimplePath path, GraphNode state){
		state = (GraphNode) circuit.findConnectionWith(path);
		if (circuit.contains(state)) return true;
		return false;
	}
/*	private boolean cycleOnPathSearch(LinkedList givenPath, LinkedList transitionSet, 
			LinkedList cycleList){
			
			/*	This function function searches a path linking the same source and target 
			 		nodes of givenPath, but containing a circuit. Nevertheless, the circuit
			 		is required to make use of the throughTransition given as parameter. If
			 		the function finds a circuit, it fills the onePathWithCircuit parameter
			 		with the found path, and notify it by returning true. 			  
			 */
			/*	Algo : max is O(2*N^2) (N is the number of transition)

				For each transition of the path search all the paths that allow input state to be reachable from himself
					if some pathes are found : 
						Add the path to the list of cycle
						
			 */
/*		
		int i;
		boolean found;
		LinkedList cycle;
		Iterator it;	
		Transition transition;	
		String stateName;
		
		
		i = givenPath.size();
	 	while(i>givenPath.size()){
	 		transition = (Transition) givenPath.get(i-1);
	 		stateName = transition.from;
	 		cycle = new LinkedList();
	 		if (isReachable(stateName, stateName, transitionSet, cycle) ){
	 			//finds possibly all the cycles going through state StateName
	 			cycleList.addAll(recursiveDirectBuildPathList(cycle, edges));
	 			found = true;
	 		}
	 		
	 		i--;
	 	}
		
	 	//Note : Cycles using more than one node of the givenPath will be found the same more than once
	 	
		return false;
	}	
/*	private boolean IsReachable(String rootStateName, String targetStateName, 
			LinkedList transitionSet, LinkedList onePath ){
		
		//search for a path between the root state and the target state (in the given transitionSet, which
		//		is a List of transition, and exposes one path, if it is reachable 
		//		(path is rendered available in parameters)
		
/*		boolean b;
		b = recursivePathSearch(rootStateName, targetStateName, transitionSet, new LinkedList(), onePath);
		return b;
	}
/*	private boolean recursivePathSearch(String rootStateName, String targetStateName, LinkedList transitionSet,
			LinkedList avoidedStates, LinkedList path){
		
		
		/*	This function returns weather or not the target state is reachable from the root state.
		   	If this functions returns true, then one among all possible path is returned through the 
		   		'path' variable (actually it appens the found path at the beginning of the 'path' variable given).
		   		Nevertheless, It excludes from the search all the avoidedStates (list of state names), 
		   		and uses only the transitionSet (list of Transition) to explore the graph. 
		 */
			/*	Algo  : Complexity maj is O(nb_transition^2) (because of avoidedStateSearch)  
			 * 
			 * 	Add State to the one being treated
			 * 
			 * 	For all transition in the transitionSet which source is rootState		
			 		if transition reaches the target
			 			found = true;
			        else 
			 			if transition target is not being treated
			 			found = recursive call
			 		if (found == true) 
			 			path.addFirst(transition);
			 			return true;
			 	return false;
			 			
			  */
/*		
		Iterator it1, it2;
		Transition transition;
		String stateName;
		boolean found=false, exist;
		
		//current state may not be further reused in the recursive search
		avoidedStates.add(rootStateName);
				
		it1 = transitionSet.iterator();
		while (it1.hasNext()){
			transition = (Transition) it1.next(); //it1.next().getClass().getName()
			
			if (transition.from.compareTo(rootStateName)==0){
				//if the transition is one available directly form the rootState
				
				if (transition.to.compareTo(targetStateName)==0){
					found = true;
				}else {
					//search if the target of the transition is one of the avoided nodes
					exist = false;
					it2 = avoidedStates.iterator();
					while(it2.hasNext() && !exist){
						stateName = (String) it2.next();
						exist = (stateName.compareTo(transition.to)==0)? true : false;
					}
					if (exist == false){
						//state is not avoided, recursive search is possible for this target
						found = recursivePathSearch(transition.to,targetStateName,transitionSet, avoidedStates, path);
					}
				} 
				
				//if path has been found, after adding the transition to the path 
				//(last transition of the list is the one pointing the targeted state )
				if (found==true){ path.addFirst(transition); return true;}
				
			}
		}
		
		
	
		return false;
	}//*/
	

	
	/* Small utilities function : ie. getting names, and other stuff used by synthesis..*/
	private String addLocalPath(String stringToModify){
		
		return addPath(localVariables , getPropClassName() , stringToModify );
		
		/*
		//String string = stringToModify; //points the original string
		Iterator it = localVariables.iterator();
		String pattern;
		Matcher matcher;
		Variables var;
		
		//for each local variables
		while (it.hasNext()){
			var = (Variables)it.next();
			pattern = var.name;
			matcher = Pattern.compile("(?m)(?s)(^\\s*(.*[^\\.\\w]+)?)"+pattern+"((\\W+.*$)|$)").matcher(stringToModify);
			
			//replace every use of this variable by its version containing the path
			while (matcher.find()){
				stringToModify = matcher.group(1)+addJMLAccessor(getPropClassName(),pattern)+matcher.group(3);
				//System.err.println("new string is "+stringToModify);
				matcher.reset(stringToModify);
			}
		}
		
		return stringToModify; */	
	}
	private String addGlobalPath(LinkedList variables, String pathToAdd, String stringToModify){
	
		return addPath(variables, pathToAdd, stringToModify);	
		
		/*
		//String string = stringToModify; //points the original string
		Iterator it = variables.iterator();
		String pattern;
		Matcher matcher;
		Variables var;

		//for each local variables
		while (it.hasNext()){
			var = (Variables)it.next();
			pattern = var.name;
			
			//stringToModify = "allowCloseTransaction := true ,\nal";//allowBeginTransaction := false";
			matcher = Pattern.compile("(?m)(?s)(^\\s*(.*[^\\.\\w]+)?)"+pattern+"((\\W+.*$)|$)").matcher(stringToModify);
			
			//replace every use of this variable by its version containing the path
			while (matcher.find()){
				
				stringToModify = matcher.group(1)+addAccessor(pathToAdd,pattern)+matcher.group(3);
				//System.err.println("new string is "+stringToModify);
				matcher.reset(stringToModify);
			}
		}
		
		return stringToModify; //*/
	}
	private String addPath(LinkedList variables, String pathToAdd, String stringToModify){
		
		//String string = stringToModify; //points the original string
		Iterator it = variables.iterator();
		String pattern;
		Matcher matcher;
		Variables var;

		//for each local variables
		while (it.hasNext()){
			var = (Variables)it.next();
			pattern = var.name;
			
			matcher = Pattern.compile("(?m)(?s)(^\\s*(.*[^\\.\\w]+)?)"+pattern+"((\\W+.*$)|$)").matcher(stringToModify);
			
			//replace every use of this variable by its version containing the path
			while (matcher.find()){
				stringToModify = matcher.group(1)+addJMLAccessor(pathToAdd,pattern)+matcher.group(3);
				//System.err.println("new string is "+stringToModify);
				matcher.reset(stringToModify);
			}
		}
		
		return stringToModify; 
	}
	private String addAccessor(String path, String variable){
		return path.trim()+"."+variable+"()";
	}
	private String addJMLAccessor(String path, String variable){
		return path.trim()+"."+variable/*+"()"*/;
	}
	private LinkedList getModifiedVariables(LinkedList variables, String string){
		//Returns a list of variables used in the given string (typically string is an update field of Transition)
		
		LinkedList modifVarList = new LinkedList();
		Iterator it = variables.iterator();
		String pattern;
		Matcher matcher;
		Variables var;
		
		//for each variable in the given list
		while (it.hasNext()){
			var = (Variables)it.next();
			pattern = var.name;
			
			//the following pattern will be efficient wether a path (e.g.: path.variable) is used or not
			matcher = Pattern.compile("(^|\\W)"+pattern+"\\s*:=.*").matcher(string);
			
			//add if variable is found to the 
			if (matcher.find()){ modifVarList.add(var);}
		}

		
		return modifVarList;
	
	}
	public  String getPropClassName(){ 
		//Generate the name of the class that will contain the automaton
		return (propertyName.substring(0,1).toUpperCase()+propertyName.substring(1,propertyName.length()) );}
	private String getStateFieldName(){
		//Defines the standard name given to the variable representing automaton state
		return "state";}
	private String getStateName(){
		/*Defines path to reach the variable representing the state from the outside of the class*/
		return (getPropClassName()+"."+getStateFieldName() );}
	private String getMethodActionName(Transition transition) {
		//Attach a String to caracterise the nature of the event that occured in method
		// which is called here "methodAction"
		String string;
		Outils o = Outils.outilsFactory();
		string = getMethodActionName(transition.mp.getMethodName(), transition.synchroTypeToString());
		return string;
	}
	private String getMethodActionName(String methodName, String synchroType){
		//Attach a String to caracterise the nature of the event that occured in method
		String string = methodName.toUpperCase()+"_";
		
		if (synchroType.compareTo("Call")==0) string += "Call"; 
		if (synchroType.compareTo("Normal Terminaison")==0) string += "NT";
		if (synchroType.compareTo("Except Terminaison")==0) string += "ET"; //*/
		
		return string;
	}
	private String getUpdateFunctionName(String varName){
		//return the name of the function associated with the modification of the variable
		//	given in parameter
		String string = varName.replaceAll(".*\\.(\\w+)","$1"); //remove prefixes
		return string;
	}
	private String getUpdateFunctionDeclaration(String varName, String methodId){
		return getUpdateFunctionName(varName)+"(int "+methodId+"); ";//{ \n";
	}
	

	
	
	/*  Accessors  */
	public boolean isSynthetizable(){
		//return wether the property has sucessfully been interpreted or not
		return succeeded;}
	public String toString(){

		String string = "";
		Iterator it1;
		Variables var;
		State state;
		Transition transition;
		 
		string += "Property name is : " + propertyName +"\n";
		string += "Local Declaration\n";
		it1 = localVariables.iterator();
		while (it1.hasNext()){
			var = (Variables)it1.next();
			string += "\t" + var.type +" "+var.name;
			if (var.initValue != null) string += "="+var.initValue;
			string += " ;\n";
		}
		string += "State List\n";
		it1 = nodes.iterator();
		while (it1.hasNext()){
			state = (State)it1.next();
			string += "\tSTATE: " + state.name +" ={\n";
			string += "\t\tref  : "+state.reference+"\n\t\ttype : ";
			if (state.type != null) { string += "standard";}
			else string += state.type;
			if (state.invariant != null) string += "\n\t\tinvariant:"+state.invariant;
			string +="\n\t}\n";
		}
		string += "Transition List\n";
		it1 = edges.iterator();
		while (it1.hasNext()){
			transition = (Transition)it1.next();
			string += "\tTransition ={\n";
			string += "\t\tfrom    : "+transition.from+"\n";
			string += "\t\tto      : "+transition.to;
			if (transition.guard != null) { string +="\n\t\tguard   : "+transition.guard;}
			if (transition.synchro != null){
				string +="\n\t\tsynchro : "+transition.synchro;
				//string += (transition.synchroEmit)? "!" : "?"; 
			}
			if (transition.update != null){string += "\n\t\tupdate  : "+transition.update;}
			string +="\n\t}\n";
		}
		string += "Parameters of the template\n";
		it1 = parameters.iterator();
		while (it1.hasNext()){
			var = (Variables)it1.next();
			string += "\t" + var.type +" "+var.name;
			if (var.initValue != null) string += "="+var.initValue;
			string += " ;\n";
		}
		
		return string;
	}
	
}
