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
public class Property implements Comparable , Cloneable{

	public String propertyName;
	public LinkedList localVariables;	//LinkedList of Variables
	public LinkedList states;			//LinkedList of State
	public LinkedList transitions;		//LinkedList of Transition
	public LinkedList parameters;		//LinkedList of Variables
	private boolean succeeded;
	
	//used for synthesis : Global Modifiers
	private static LinkedList ModifiedListGlobalVar			= new LinkedList(); //store at synthesis time the global Var used
	private static LinkedList updateMethodListGlobalVar		= new LinkedList();	//stores in the same order, the body of the method generated for modification
	private static LinkedList updateMethodannotationList	= new LinkedList(); //stores in the same order, the annotation associated
	private static LinkedList updateMethodelseAnnotationList= new LinkedList(); //stores in the same order, info to generate the 'else' annotation

	
	Property(Node template) {
		
		Outils o = Outils.outilsFactory();
		propertyName = "";		
		localVariables = new LinkedList();                                                                                                   
		states = new LinkedList();			
		transitions = new LinkedList();		 
		parameters = new LinkedList();  	
		
		succeeded = extractProperty(template);
		modifyTransitionRef();
	}

	
	
	/*
	 * Modifying Functions
	 * 
	 */
	
	
	/*Synthesize the class representing the automaton
		reference should be shared by every method dealing with the current automaton */
	public String synthesizeAutomatonClass(LinkedList globalVariables, String globalPath){
		
		String string="";

		
		string += "public class "+getPropClassName()+" { \n";
		
		string += synthetizeClassVariables(globalVariables, globalPath);
		string += synthetiseClassModifiers(globalVariables, globalPath);
		
		string += "\n\n}";
		return string;	
	}
	public String synthesizeGlobalClass(LinkedList globalVariables, String globalPath){
		
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
					tmp1 += "\tpublic static /*@ pure @*/ "+var.getInterpretedType()+" "+var.name;
					tmp1 +="() {return "+var.name+";}\n";
					string += "\tprivate static /*@ spec_public @*/ "+var.getInterpretedType()+" "+var.name;
					if (var.initValue.compareTo("") != 0 ) { string += " = "+var.initValue+" ;"; }
					else string += " ;";
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
	/*Synthesize the annotation for every methods (instanceof MethodProperty) for the current property
		This function returns a list of MethodProperty, filled with the appropriate annotations 
		The list of globalVariable is compulsary to be able to generate the modifies clause*/
	public LinkedList synthesizeMethods(LinkedList globalVariables, String globalPath){
		
		LinkedList finalList;
		Iterator it ;	
		
		//To be completed to be truly correct... (cf counterExample.xml)
		//finalList = synthetizeTransition(globalVariables);
		finalList = synthetiseMethodPropertyList(globalVariables, globalPath);
		return finalList;
	}
	
	
	/*Function renaming parameters, which is typically done at instanciation time 
	 	when parameters of the model are linked with global variables */
	public boolean renameParameters(LinkedList newParamList){

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
				it3 = transitions.iterator();
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
				it3 = states.iterator();
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
	
	
	/*Functions implementing interfaces */
	public int compareTo(Object obj){
		
			int i;
			Property prop2;
			
			if(!(obj instanceof Property)) throw new ClassCastException();
			prop2=(Property)obj;
			i = this.propertyName.compareTo(prop2.propertyName);
						
			return i;
		}
	protected Object clone()  throws CloneNotSupportedException
	{ 
		LinkedList list = new LinkedList();
		Iterator it;
	    State state;
	    Transition transition;
	    Variables var;
	    String string;
		Property copy = (Property)super.clone();

		//deep copy of states (compulsary for parameters renaming)
	    it=states.iterator();
	    while (it.hasNext()){
	    	state = (State)it.next(); 
	    	state = (State)state.clone();
	    	list.add(state);
	    }
	    copy.states = list;//*/
	    
	    //deep copy of transitions (compulsary for parameter renaming, and synchro linkage with MethodProperty)
	    list = new LinkedList();
	    it=transitions.iterator();
	    while (it.hasNext()){
	    	transition = (Transition)it.next(); 
	    	transition = (Transition)transition.clone();
	    	list.add(transition);
	    }
	    copy.transitions = list; 
	    
	    //deep copy of parameters
	    list = new LinkedList();
	    it=parameters.iterator();
	    while (it.hasNext()){
	    	var = (Variables)it.next(); 
	    	var = (Variables)var.clone();
	    	list.add(var);
	    }
	    copy.parameters = list;
	    
	    
	    
	    return copy;
	  }	
	

	/*
	 * 	Internal modifying functions  
	 * 
	 */
	
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
					tmp1 += "\tpublic static /*@ pure @*/ "+var.getInterpretedType()+" "+var.name;
					tmp1 +="() {return "+var.name+";}\n";
					string += "\tprivate static /*@spec_public@*/ "+var.getInterpretedType()+" "+var.name; //cf:  http://java.about.com/od/beginningjava/l/aa_file_struct.htm
					if (var.initValue.compareTo("") != 0 ) { string += " = "+var.initValue+" ;"; }
					else string += " ;";
					string += " \n";
				}else System.err.println ("Channel "+var.name+" should not be local (Ignored by synthesis)");
			}while (it1.hasNext());	
			string += tmp1;
		}
		else{string += "\t//(None to be added)\n";};
		 
		
		
		//insert states definition
		string += "\n\n\t//State Definition\n";
		stateName = getStateFieldName();//propertyName+"State";
		tmp1 = "\tpublic static int "+stateName+" = ";
		i = 0 ;
		it1 = states.iterator();
		while (it1.hasNext()){
			state= (State)it1.next();
			string += "\tpublic final static int "+state.stateName+" = "+i+" ; \n"; 
			if (state.isInitial()) tmp1 +=state.stateName+" ;\n";
			//TODO invariant would surely need to be interpreted or splitted to several invariants
			if (state.invariant.compareTo("")!=0){ 
				invariants += "\t//@ static invariant ("+stateName+"=="+state.stateName+") ==> (";
				invariants += addLocalPath(addGlobalPath(globalVariables,globalPath,state.invariant))+") ; \n";
			}
			invariant2 += "\t              "+stateName+"=="+state.stateName+" || \n";
			i++;
		}
		string += tmp1 + "\n\t//states invariants\n";
		i = invariant2.lastIndexOf('|');
		invariant2 = "\t/*@ static invariant ("+invariant2.substring(15, i-2)+" ); \n\t@*/ \n";
		
				
		//insert invariants of the property
		string += invariant2; //describes possible states of the automaton
		string += invariants; //contains all the states invariants
		
		//string += synthetizeFucntions();
		
		
		
		return string;	
	
	}
	
	/** TODO - do the same as for local variables with Global variables **/
	private String synthetiseClassModifiers(LinkedList globalVariables, String globalPath){
		
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
		Collections.sort(transitions); //sort using first the 'from' field
		it =  transitions.iterator();
		while (it.hasNext()){
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
				prefixedCond = methodId+"=="+prefix+"."+getMethodActionName(tmpTransition.synchro, tmpTransition.synchroType); 
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
				
				//add path to the global and global variables			
				tmpTransition.guard =  addJMLGlobalPath(globalVariables, globalPath, tmpTransition.guard);
				tmpTransition.update = addJMLGlobalPath(globalVariables, globalPath, tmpTransition.update);
				
				//build the general condition for modification
				prefixedCond = methodId+"=="+prefix+"."+getMethodActionName(tmpTransition.synchro, tmpTransition.synchroType); 
				prefixedCond += " && "+prefix+"."+state+"=="+prefix+"."+tmpTransition.from;
				if (tmpTransition.guard.compareTo("true")!=0 || tmpTransition.guard.compareTo("")!=0)
					prefixedCond += " && "+tmpTransition.guard; 
				
				
				
				//add path to the global and global variables			
				tmpTransition.guard =  addGlobalPath(globalVariables, globalPath, transition.guard);
				tmpTransition.update = addGlobalPath(globalVariables, globalPath, transition.update);
			
				//affectation of the state to modifiable and propertyList if not already there
				localModifiedVar = new LinkedList();
				localModifiedVar.addAll(getModifiedVariables(localVariables, tmpTransition.update));

				//build the general condition for modification
				cond = methodId+"=="+getMethodActionName(tmpTransition.synchro, tmpTransition.synchroType); 
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
				if (tmp.compareTo(tmpTransition.from)!=0) {
					goNextBody += indent2+"break;\n";
					goNextBody += indent1+"case "+tmpTransition.from+":\n";
					tmp = tmpTransition.from;
				}
				goNextBody += indent2+"if ("+cond+") \n"+indent3+"return "+tmpTransition.to+";\n";
				
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
					//System.err.println("serching for: "+searchedVar.name);
					//search if this variable is already in the list 
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
						
						currentVarName = searchedVar.name;
						currentAnnotations = "\t//@ modifies "+searchedVar.name/*+"\\nothing"*/+"; \n";
						currentFunctionBody = "\t public static void"/*+searchedVar.getInterpretedType()*/;
						currentFunctionBody+= " "+getUpdateFunctionDeclaration(searchedVar.name, methodId);
						currentElseAnnotation = "";
					}
					else {
						found = false;
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
						currentFunctionBody  += indent1+"if ("+cond+" && "+state+"=="+tmpTransition.from+") {\n"+indent2+searchedVar.name+"="+updateAffectation+"; return; } \n";
						currentElseAnnotation+= indent1+"!("+prefixedCond+") && \n";
					
					}else System.err.println("Update expression not found for variable: "+searchedVar.name);
					
					varNameList.add(searchedVar.name);
					annotationList.add(currentAnnotations);					
					updateMethodList.add(currentFunctionBody);
					elseAnnotationList.add(currentElseAnnotation);
					
				}
			}
			
													
			/*Build here the method Reference*/
			methodNameList.add(getMethodActionName(tmpTransition.synchro, tmpTransition.synchroType));
		
			
		}

		tmp2 = "";
		k = 0;
		Collections.sort(methodNameList);
		it = methodNameList.iterator();
		while (it.hasNext()){
			tmp = (String) it.next();
			if (tmp.compareTo(tmp2) != 0 ){string += "\tpublic final static int "+tmp+" = "+k+"; \n" ; k++; tmp2 = tmp;}
		}
		
		
		/* finalise goNext() stuff */
		goNextBody = goNextBody.substring(goNextBody.indexOf("\n")); //remove the first break !
		goNextBody = "\tpublic static /*@pure@*/ int goNext(int "+methodId+/*", int "+state+*/"){\n"+indent1+"switch("+state+"){\n"+goNextBody;
		goNextBody += indent3+"break;\n"+indent2+"default : break;\n"+indent1+"}\n"+indent1+"return "+state+";\n\t}\n";
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
	private void   addToGlobalModifiers(Transition tmpTransition, LinkedList globalModifiedVar, String prefixedCond,
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
				currentFunctionBody+= " "+searchedVar.name+"(int "+methodId+/*", int "+state+*/"){ \n";
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
				currentFunctionBody  += indent1+"if ("+prefixedCond+") { \n"+indent2+searchedVar.name+"="+updateAffectation+"; return; } \n";
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
				currentFunctionBody += indent1+"else return "+/*currentVarName+*/"; \n\t}\n";
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
	
	
	
	
	
	/** TODO **/
	private LinkedList synthetiseMethodPropertyList(LinkedList globalVariables, String globalPath){
	
		/* Algo
		 	

		*/

		int i,j;
		boolean found;
		Iterator it;
		LinkedList finalList = new LinkedList();
		LinkedList mpList = new LinkedList();
		LinkedList outTransitionList, inTransitionList;
		LinkedList modifiedVariableList;
		LinkedList prefixedGlobalVariables = new LinkedList();
		LinkedList prefixedLocalVariables  = new LinkedList();
		LinkedList updateList;
		Transition inTransition, outTransition, tmpTransition;
		Variables var;
		String[] updateParam = new String[1];
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
		i = transitions.size();
		while(i>0){
			inTransition = (Transition) transitions.get(i-1);
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
			//System.err.println("current call transition is: "+i);
			inTransition = (Transition) inTransitionList.get(i-1);
			//System.err.println("Operating method Call through transition:"+inTransition);
			
			updateParam[0] = getPropClassName()+"."+getMethodActionName(inTransition.synchro, inTransition.synchroType);
			
			j=outTransitionList.size();
			while(j>0){
				//System.err.println("j="+j);
				outTransition = (Transition) outTransitionList.get(j-1);
				if (outTransition.mp.getMethodName().compareTo(inTransition.mp.getMethodName())==0) {
					
					//System.err.println("Operating on the following \"return\" transition: "+outTransition);
										
					//Evaluate the possible outputPoints
					if (compatiblePath(inTransition, outTransition)) {
						
						//System.err.println("The previous \"return\" transition is compatible with \"Call\" transition");
						
						//preparation phase
						mp = inTransition.mp;
						try {tmpTransition = (Transition) outTransition.clone();}
						catch(Exception e){ 
							tmpTransition = outTransition; 
							System.err.println("Transition.clone() failed, resulting in potentially corrupted prefix");
						}
						
						tmpTransition.guard = addJMLGlobalPath(globalVariables, globalPath, tmpTransition.guard);
						tmpTransition.guard = addJMLGlobalPath(localVariables, getPropClassName(),tmpTransition.guard);
						tmpTransition.update= addJMLGlobalPath(globalVariables, globalPath, tmpTransition.update);
						tmpTransition.update= addJMLGlobalPath(localVariables, getPropClassName(),tmpTransition.update);
						modifiedVariableList = getModifiedVariables(prefixedGlobalVariables,tmpTransition.update);
						modifiedVariableList = getModifiedVariables(prefixedLocalVariables ,tmpTransition.update);
						
						
						updateList = new LinkedList();
						for (int k=modifiedVariableList.size() ; k>0 ; k--) 
							updateList.add(getPropClassName()+"."+getUpdateFunctionName(((Variables)modifiedVariableList.get(k-1)).name));
						
						//affectation to the MethodProperty
						mp.addModifies(modifiedVariableList);
						
						if (outTransition.synchroTypeToString().compareTo("Normal Terminasion")==0){
							mp.addNormalPostcond(getStateFieldName(),getPropClassName(), inTransition, tmpTransition);
							for(int k=updateList.size()-1 ; k>=0 ; k--) mp.addNormalExitActions((String)updateList.get(k), updateParam);
						}else{
							mp.addExceptPostcond(getStateFieldName(),getPropClassName(), inTransition, tmpTransition);
							for(int k=updateList.size()-1 ; k>=0 ; k--)mp.addExceptExitActions((String)updateList.get(k), updateParam);
						}
					}else {
						//System.err.println("Transition "+inTransition);
						System.err.println(propertyName+" : No path reaching the transition starting at "+
							inTransition.from+" with synchro "+inTransition.mp.getMethodName()+" (transition ignored)\n");
					}
				}
				else {/*System.err.println("Following Transition is not associated to the right method: "+outTransition);*/}
				j--;
			}
			//all possible terminaison have been treated (if any)
			try {tmpTransition = (Transition) inTransition.clone();}
			catch(Exception e){ 
				tmpTransition = inTransition; 
				System.err.println("Transition.clone() failed, resulting in potentially corrupted prefix");
			}
			mp = inTransition.mp;
			mpList.add(mp);
			tmpTransition.guard = addJMLGlobalPath(globalVariables, globalPath, tmpTransition.guard);
			tmpTransition.guard = addJMLGlobalPath(localVariables, getPropClassName(),tmpTransition.guard);
			tmpTransition.update= addJMLGlobalPath(globalVariables, globalPath, tmpTransition.update);
			tmpTransition.update= addJMLGlobalPath(localVariables, getPropClassName(),tmpTransition.update);
			modifiedVariableList = getModifiedVariables(prefixedGlobalVariables,tmpTransition.update);
			modifiedVariableList = getModifiedVariables(prefixedLocalVariables ,tmpTransition.update);

			
			updateList = new LinkedList();
			for (int k=modifiedVariableList.size() ; k>0 ; k--) {
				updateList.add(getPropClassName()+"."+getUpdateFunctionName(((Variables)modifiedVariableList.get(k-1)).name));
				System.err.println("Modifying variable: "+((Variables)modifiedVariableList.get(k-1)).name);
			}
			
			//affectation to the MethodProperty
			mp.addPrecond(getStateFieldName(),getPropClassName(), tmpTransition);
			for(int k=updateList.size()-1 ; k>=0 ; k--) mp.addEntryActions((String)updateList.get(k), updateParam);
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
		
		
		it = finalList.iterator();
		while (it.hasNext()){
			mp = (MethodProperty) it.next();
			mp.releaseAutomaton(getPropClassName(),getStateFieldName(), "goNext", updateParam);	
		}
				
		return finalList;
		
	}
	private boolean compatiblePath(Transition transitionCall, Transition transitionTerm){
		
		/* Returns weather or not a compatible path has been found to link transitionCall to 
		 		its associated terminaison */
			
		
		/*	Algo
		 * 
		 * 		list = cheminCourant
		 * 		pathList = liste des chemins (list of list)
		 * 		tmp_lists = liste des chemins alternatifs (variable temporaire)
		 * 		transitionList = {transitions}
		
				TODO
		
		 		return pathList;		
		*/
		
		 int depth=1, tmpDepth, i, j, k;
		 boolean isReachable;
		 boolean stop;
		 Iterator it;
		 LinkedList onePath = new LinkedList();
		 LinkedList allPath = new LinkedList();
		 LinkedList cycleList = new LinkedList();
		 Transition transition;
		 
		 isReachable = isReachable(transitionCall.to, transitionTerm.from , transitions, onePath);
		 if (isReachable){
		 	
		 	allPath = recursiveDirectBuildPathList(onePath, transitions);
		 	//allPath now contains a list of path (i.e. a list of transition list) of minimal size() equal to 1
		 
		 	//Explore all path to find a compatible depth of method Call & return
			i = allPath.size();
		 	while(i>0 && depth !=0){	//
				onePath = (LinkedList) allPath.get(i-1);
		 		
		 		it = onePath.iterator();
		 		depth=0; //depth represents the number of recursive call for the method
		 		//evaluation of the depth of the path
		 		while(it.hasNext()){
		 			transition = (Transition) it.next();
		 			if (transition.mp.getMethodName().compareTo(transitionCall.mp.getMethodName())==0){
		 				if (transition.synchroTypeToString().compareTo("Call")==0){depth ++;}
		 				else { depth --; } //it is obviously a terminasion
		 			}
		 		}
		 	}
		 
		 	if (depth!=0) {System.err.println("Search if any cycle can make the transition compatible");}
		 	
		 	//If it has been impossible to find one "direct path", search for cycle that compensate
		 	// The difference between call and return depth	
		 	i = allPath.size();
		 	while(i>0 && depth !=0){
		 		
		 		onePath = (LinkedList) allPath.get(i-1);
		 		
		 		//find all possible cycles 
				cycleOnPathSearch(onePath, transitions, cycleList);
				tmpDepth=0;
				it = cycleList.iterator();
				while (it.hasNext() && depth!=0){
					//evaluation of each cycle found
					onePath = (LinkedList) it.next();
					
					//analyzing the depth of the cycle
					k = onePath.size();
					while(k>0){
						transition = (Transition) onePath.get(k-1);
						if (transition.mp.getMethodName().compareTo(transitionCall.mp.getMethodName())==0){
							if (transition.synchroTypeToString().compareTo("Call")==0){tmpDepth ++;}
							else { tmpDepth --; } //it is obviously a terminasion
						}
					}
				
					//Search if any j*tmpDepth+depth = 0 
					//	integer j is the number of times the cycle should be taken to make the terminaison possible
					{
						j=0;
						//descrimiate implicitely cases in which the solution would diverge
						if (depth >0 && tmpDepth<0){ 	for(j=1 ; depth+i*tmpDepth > 0 ; j++); }
						else if (depth<0 && tmpDepth>0){for(j=1 ; depth+i*tmpDepth < 0 ; j++); }
						
						if (depth+i*tmpDepth==0) depth=0;
					}
				}
				
				i--;			
			}
	 		
		 }//ends the reachability condition

		 
		return (depth==0);
		
	}
	// functions on graph/automaton
	private LinkedList recursiveDirectBuildPathList(LinkedList givenPath, LinkedList transitionSet){
		
		/*	Given a certain path, this function returns the list of all equivalent path 
		 		(i.e. all the path, that may be found out of the transitionSet, to link the
		 		source state to the target state of the givenPath). The givenPath
		 		variable is a list of transition starting from a source state, and reaching a
		 		target state.
		 	The returned list is a List of Path (namely, a list of transition list)
		 
		 	!!! This function returns all "non-circuit" path
		 */
		
		
		
		/*	Algorithm: Complexity ~(N^3)
		 
		 	SOURCE =  ((Transition)givenPath.getFirst()).from;
		 	TARGET =  ((Transition)givenPath.getLast()).to;
		 
		 	while all givenPath hasn't been explored
		 		remove the last transition form the transitionSet
		 		find if there is another path originated from the SOURCE that reaches the same target as the removed transition
		 		if so
		 			callRecursively this method
		 			Concatenate the alternative paths obtained with the queu explored that reaches the TARGET
		 			add those alternative Paths to the List of path
		 		
		 		maintain the queu by adding the current transition considered in this loop
		 	
		 	Rebuild the transitionSet
		 	Add the given path to the returned list of Path
		*/
		
		//Avoid the case in which the path is void
		Iterator it = givenPath.iterator();
		if (!(it.hasNext())) return givenPath;
		
		
		//Extract the source and target of path
		String rootStateName = ((Transition)givenPath.getFirst()).from;
		String targetStateName= ((Transition)givenPath.getLast()).to;
		
		
		//Create the list of path, which is basically 
		//	the concatenation of the givenPath and all others alternative path 
		LinkedList pathList = new LinkedList();
		

		//create temporary variables for the search
		String currentState;
		Transition lastTransition, transition;
		Iterator it1;
		LinkedList tmpList;
		LinkedList alternativePath;
		LinkedList complementaryPath  = new LinkedList();
		LinkedList removedTransitions = new LinkedList();
		boolean found = false;
		int j ;
		
		for (int i=givenPath.size() ; i>0 ; i--){
			
			lastTransition = (Transition) givenPath.get(i-1); // equivalent to removeLast()
			
			//remove the last transition from the possible transitions to prepare the search for alternative path
			it1 = transitionSet.iterator(); j=0 ; found = false;
			while (it1.hasNext() && found==false){
				transition = (Transition) it1.next();
				if (lastTransition.compareTo(transition)==0) {found = true;}
				else j++;
			}
			if (found) {removedTransitions.add(transitionSet.remove(j));}
			
			//Search if there is any alternative Path
			currentState = lastTransition.to;
			alternativePath = new LinkedList();
			if ( isReachable(rootStateName, currentState, transitionSet, alternativePath)){
				//alternativePath has been set implicitely and is a Path (list of transition)
				alternativePath = recursiveDirectBuildPathList(alternativePath , transitionSet);
				//alternativePath now contains a list of path from source to the current state
				it1 = alternativePath.iterator();
				while (it1.hasNext()){
					tmpList = (LinkedList) it1.next();
					tmpList.addAll(complementaryPath);
				}
				//alternativePath now is a list of Path linking the original source with the final target
				pathList.addAll(alternativePath);
				
				//pathList has been updated with the list of new paths
			}
			
			//complementary path contains the part of the givenPath already explored
			complementaryPath.add(lastTransition);
			
		}
		
		//restore the transitionSet
		transitionSet.addAll(removedTransitions);
		
		//add the given path to the list as this path is also part of the solution
		pathList.add(givenPath);
		
		
		return pathList;
		
	}
	private boolean cycleOnPathSearch(LinkedList givenPath, LinkedList transitionSet, 
			LinkedList cycleList){
			
			/*	This function function searches a path linking the same source and target 
			 		states of givenPath, but containing a circuit. Nevertheless, the circuit
			 		is required to make use of the throughTransition given as parameter. If
			 		the function finds a circuit, it fills the onePathWithCircuit parameter
			 		with the found path, and notify it by returning true. 			  
			 */
		
			
			/*	Algo : max is O(2*N^2) (N is the number of transition)

				For each transition of the path search all the paths that allow input state to be reachable from himself
					if some pathes are found : 
						Add the path to the list of cycle
						
			 */
		
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
	 			cycleList.addAll(recursiveDirectBuildPathList(cycle, transitions));
	 			found = true;
	 		}
	 		
	 		i--;
	 	}
		
	 	//Note : Cycles using more than one node of the givenPath will be found the same more than once
	 	
		return false;
	}	
	private boolean isReachable(String rootStateName, String targetStateName, 
			LinkedList transitionSet, LinkedList onePath ){
		
		//search for a path between the root state and the target state (in the given transitionSet, which
		//		is a List of transition, and exposes one path, if it is reachable 
		//		(path is rendered available in parameters)
		
		boolean b;
		b = recursivePathSearch(rootStateName, targetStateName, transitionSet, new LinkedList(), onePath);
		return b;
	}
	private boolean recursivePathSearch(String rootStateName, String targetStateName, LinkedList transitionSet,
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
					//search if the target of the transition is one of the avoided states
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
	}
	

	

	
	
	
	
	
	
	
	
	
/*	
	
	//return the synthesized methodProperty with adequate annotations
	// TODO Add functionnality to generate correct postcond (see counterExample.xml) e.g. take into
	//account updates of call transitions in the ensures/signals postconditions !!
	//For the moment, avoid the use of the variables updated after calling the method, in the postconditions. 
	private LinkedList synthetizeTransitionLight(LinkedList globalVariables, String globalPath){ 
		
		Transition transition;
		MethodProperty mp, mp2;
		String guard;
		String update;
		String source;
		LinkedList prefixedGlobalVariables = new LinkedList();
		LinkedList varNames ; //used for modifies
		Variables var = new Variables();
		Transition tmpTransition ;
		//LinkedList awaitingStates = new LinkedList();
		LinkedList mpList = new LinkedList();
		LinkedList finalList = new LinkedList();
		Iterator it = transitions.iterator();
		Iterator it2;
			
		String propertyClassName = getPropClassName();
		String StateName = getStateName(); 
		String instName = getPropClassName();
		String statePrefix = getPropClassName()+".";

		
		//Building the prefixedGlobalVariable list
		it2 = globalVariables.iterator();
		while (it2.hasNext()){
			var = (Variables)it2.next();
			try{ var = (Variables) var.clone();}
			catch(Exception e){ 
				System.err.println("Variables.clone() failed, resulting in potentially corrupted prefix for global Variables");}
			var.name = globalPath+"."+var.name;
			prefixedGlobalVariables.add(var);
		}
		
		
		it = transitions.iterator();
		while (it.hasNext()){
			transition = (Transition) it.next();
			try {tmpTransition = (Transition) transition.clone();}
			catch(Exception e){ 
				tmpTransition = transition; 
				System.err.println("Transition.clone() failed, resulting in potentially corrupted prefix");}
			/*mp = transition.mp;
			guard  = transition.guard;
			update = transition.update;//
			mpList.add(tmpTransition.mp);
			
			//add new state of the automaton (if needed) to the methodProperty (affect modifyable and propertyList private fields) 
			tmpTransition.mp.addState(propertyClassName);
			
			//modify guard and sychro field to access local Variable of the given propertyClassName
			//System.err.println("Adding local path to transition"+transition);
			tmpTransition.guard = addLocalPath(tmpTransition.guard);
			tmpTransition.guard = addGlobalPath(globalVariables, globalPath, tmpTransition.guard);
			tmpTransition.update = addLocalPath(tmpTransition.update);
			tmpTransition.update = addGlobalPath(globalVariables, globalPath, tmpTransition.update);
			

			//affectation of the state to modifiable and propertyList if not already there
			var.name = StateName;
			varNames = new LinkedList();
			varNames.add(var);
			varNames.addAll(getModifiedVariables(localVariables, tmpTransition.update));
			varNames.addAll(getModifiedVariables(prefixedGlobalVariables, tmpTransition.update));				
			tmpTransition.mp.addModifies(varNames);


			//add compulsary precondition and entry actions 
			if (transition.synchroTypeToString().compareTo("Call")==0){
				tmpTransition.mp.addPrecond(StateName, statePrefix, tmpTransition);
				tmpTransition.mp.addEntryActions(StateName, statePrefix, tmpTransition);
			}else if (transition.synchroTypeToString().compareTo("Except Terminasion")==0){
				//add compulsary postcondition and exit actions
				tmpTransition.mp.addExceptPostcond(StateName, statePrefix, tmpTransition);
				tmpTransition.mp.addExceptExitActions(StateName, statePrefix, tmpTransition);
			}else if (transition.synchroTypeToString().compareTo("Normal Terminasion")==0){
				//add compulsary postcondition and exit actions
				tmpTransition.mp.addNormalPostcond(StateName, statePrefix, tmpTransition); 
				tmpTransition.mp.addNormalExitActions(StateName, statePrefix, tmpTransition);
			}else System.err.println("Transition is of type ["+transition.synchroTypeToString()+"]" );
					
		}


				
		//Remove multiple references to the same MethodProperty
		//System.out.println("Removing double references\n\n");
		mp = new MethodProperty("",""); 
		Collections.sort(mpList);
		it = mpList.iterator();
		while (it.hasNext()){
			mp2 = mp;
			mp = (MethodProperty) it.next(); 
			
			if (mp.compareTo(mp2)!= 0 ){finalList.add(mp);}
		}
		
		
		//Complete the annotation with knowledge acquiered on the whole automaton
		// 	While the automaton is stucked in states which are waiting for a specific method terminaision
		// 	any method can be called, except the one already declared for the state with call ('!' in synchro);
		// 	requires statements must allow these methods to be called. "mp.addMethodEntryPoints(StateName, states)" will do so  
		it = finalList.iterator();
		while (it.hasNext()){
			mp = (MethodProperty) it.next();
			mp.releaseAutomaton();						//release the automaton for each MethodProperty
		}
				
		return finalList;
	}
		
*/	
	//Function used for concatenating a path "$propertyClassName.", before every local variable of the stringToModify
	private String addLocalPath(String stringToModify){
		
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
		
		return stringToModify; 
		
	}
	private String addGlobalPath(LinkedList variables, String pathToAdd, String stringToModify){
		
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
		
		return stringToModify; 
	}
	private String addJMLGlobalPath(LinkedList variables, String pathToAdd, String stringToModify){
		
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

	//Generate the name of the class that will contain the automaton
	public String getPropClassName(){ 
		return (propertyName.substring(0,1).toUpperCase()+propertyName.substring(1,propertyName.length()) );}
	//Defines the standard name given to the variable representing automaton state
	private String getStateFieldName(){return "state";}
	//Defines the name under which the Property will be instanciated
/*	private String getPropInstName(){
		return (propertyName.substring(0,1).toLowerCase()+propertyName.substring(1,propertyName.length()) );}*/
	/*Defines path to reach the variable representing the state from the outside of the class
	  	var parameter should be an instance of the automaton class implementing the current property*/
	private String getStateName(){ return (getPropClassName()+"."+getStateFieldName() );}
	private String getMethodActionName(String synchro, int synchroType) {
		String string;
		Outils o = Outils.outilsFactory();
		
		string = (synchro.substring(0,1).toUpperCase()+synchro.substring(1,synchro.length()) );
		
		/*if (o.synchroTypeToString(synchroType).compareTo("Call")==0) string += "Call"; 
		if (o.synchroTypeToString(synchroType).compareTo("Normal Terminasion")==0) string += "_NT";
		if (o.synchroTypeToString(synchroType).compareTo("Except Terminasion")==0) string += "_ET"; //*/
		
		return string;
	}
	private String getUpdateFunctionName(String varName){
		String string = varName.replaceAll(".*\\.(\\w+)","$1"); //remove prefixes
		return string;
	}
	private String getUpdateFunctionDeclaration(String varName, String methodId){
		return getUpdateFunctionName(varName)+"(int "+methodId+/*", int "+state+*/"){ \n";
	}
	
	/* Functions used to extract property, and preparing it ready for synthesis*/
	//extract property given under the form of a DOM Node
	private boolean extractProperty(Node node){
		
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
					if (state.isGoodState() ) {
						states.add(state);
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
					state = findMethodName(string);
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
	//rename every state references in transition by its user defined state name
	private void modifyTransitionRef(){
	
		Iterator it1, it2;
		Transition transition;
		State state;
		
		it1 = states.iterator() ;
		while (it1.hasNext()){
			state = (State)it1.next();


			it2 = transitions.iterator();
			while (it2.hasNext()){
				transition = (Transition)it2.next();			
				if (transition.from.compareTo(state.reference)==0){
					transition.from = state.stateName;};
				if (transition.to.compareTo(state.reference)==0){
					transition.to = state.stateName; };
			}//normally, both 'from' and 'to' fields should have changed
			 //unless state hasn't been given a name
			
		}
	
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
	private State findMethodName(String reference) {
		State state;
		Iterator iter = states.iterator();
		while (iter.hasNext() ){ 
			state = (State)iter.next();
			if (reference.compareTo( state.reference) == 0) return state ;
		}
		return null;
	}

		
	
	
	/*
	 * 	Access functions  
	 * 
	 */
	
	//return wether the property has sucessfully been interpreted or not
	public boolean isSynthetizable(){ return succeeded;}
	//Display function
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
		it1 = states.iterator();
		while (it1.hasNext()){
			state = (State)it1.next();
			string += "\tSTATE: " + state.stateName +" ={\n";
			string += "\t\tref  : "+state.reference+"\n\t\ttype : ";
			if (state.type != null) { string += "standard";}
			else string += state.type;
			if (state.invariant != null) string += "\n\t\tinvariant:"+state.invariant;
			string +="\n\t}\n";
		}
		string += "Transition List\n";
		it1 = transitions.iterator();
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
