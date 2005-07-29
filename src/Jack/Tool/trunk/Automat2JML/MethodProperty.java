/*
 * Created on Mar 11, 2005
 *
 * TODO To change the template for this generated file go to
 * Window - Preferences - Java - Code Style - Code Templates
 */

/**New requires will look
 * @author tdupont
 * 
 * TODO To change the template for this generated type comment go to Window -
 * Preferences - Java - Code Style - Code Templates
 */


import java.util.Collections;
import java.util.LinkedList;
import java.util.Iterator;
import java.util.regex.*;


public class MethodProperty implements Comparable{

	
	//Method identifier fields
	private String ownerClass;			
	private String classDefinition;
	private String methodName;
	private String methodDefinition;
	
	//Method annotation fields (all the below list fields are LinkedList of String)
	//private LinkedList propertyList; 		//list the propertyClassName attached to the method (list of String element).
	private LinkedList precondition;		//JML form of the precondition (list of String).
											//A unique string is built up for each automaton (each element of the list 
											// corresponds to a different automaton)
	private LinkedList postcondition;		//JML form of the normal postcondition (list of String element)
	private String     modifiable;			//List of the modifies, get method returns the JML form of it 
	private LinkedList signals;				//JML form of the exceptional postcondition (list of String element)
	private LinkedList entryActions;		//JML form of the entry actions (list of String element)
	private LinkedList normalExitActions;	//JML form of the exit-actions (to be added after 'return') (list of String element)
	private LinkedList exceptExitActions;	//JML form of the exit-actions (to be added after 'throw') (list of String element)

	

	
	//temp variables, used between add a new property and releasing it
	private boolean exceptTermUsed;
	
	
	
	
	//-----------------------------------------------------
	// Constructor 
	MethodProperty( String className, String methodName) {
		ownerClass = className ;
		classDefinition = "" ;
		this.methodName = methodName;
		methodDefinition = "" ;
		
		
		precondition = new LinkedList();
			String string = "";
			precondition.add(string);
		postcondition = new LinkedList();
		modifiable = "";
		signals = new LinkedList();
		entryActions = new LinkedList();
		normalExitActions = new LinkedList();
		exceptExitActions = new LinkedList();
		
		
		exceptTermUsed = false;
	}
	//-----------------------------------------------------
	
	/*
	 *   Manipulation functions
	 * 
	 */

	/*Functions used to set UPPAAL annotation helping the identification of function*/
	public void setClassDefinition(String string) {classDefinition  = string;}
	public void setMethodDefinition(String string){methodDefinition = string;}
	
	
	//Functions combining properties
	public void addPrecond (String stateName, String StateDeclarationPrefix ,Transition transition){
		//define how preconditions are combined
		String string = (String) precondition.removeLast();
		StateDeclarationPrefix = StateDeclarationPrefix+".";
		string += "("+StateDeclarationPrefix+stateName+"=="+StateDeclarationPrefix+transition.from+" && ("+transition.guard+") ) \n";
		precondition.add(string);
	}
	public void addModifies (LinkedList varNames){
		//adds a list of variable to the modifiable list if not already there
		Variables var;
		LinkedList tmpList = new LinkedList();
		Iterator it, it2;
		String string;
		
		//add conditionaly the variable to modified list
		it = varNames.iterator();
		while (it.hasNext()){
			var =(Variables) it.next();
			if (!( Pattern.compile(" "+var.name+" ").matcher(modifiable).find() ))
			{  	
				//a new variable (unmodified yet) is being added
				if (modifiable.compareTo("")!=0) modifiable += ", "+var.name+" ";
				else modifiable += " "+var.name+" ";
			}
		}
	}
	public void addNormalPostcond (String stateName, String StateDeclarationPrefix ,
			Transition inTransition, Transition outTransition){
		
		/*creates a new postcondition the given transition, accessing modifiing states and affecting new state value 
	 		(rendered available by the given prefix)
			
		  Also define how postconditions are combined */
		StateDeclarationPrefix = StateDeclarationPrefix+".";
		String post = "(\\old("+StateDeclarationPrefix+stateName+")=="+StateDeclarationPrefix+inTransition.from;
		post +=" && ("+outTransition.guard+") ) ==> ";
		post += "("+StateDeclarationPrefix+stateName+"=="+StateDeclarationPrefix+outTransition.to;
		post += ") \n";
		postcondition.add(post);
	}
	public void addExceptPostcond (String stateName, String StateDeclarationPrefix ,
			Transition inTransition, Transition outTransition){
		
		/*creates a new postcondition the given transition, accessing modifiing states and affecting new state value 
 			(rendered available by the given prefix)
		
		  Also define how postconditions are combined */

		
		//TODO : Enhancement 
		// change " (Exception e) ... "  for
		//(Exception e) instanceof ExceptionType ==> ( ..... )
		StateDeclarationPrefix = StateDeclarationPrefix+".";
		String Exceptpost = "(Exception e) (\\old("+StateDeclarationPrefix+stateName+")==";
		Exceptpost += StateDeclarationPrefix+inTransition.from+" && ("+outTransition.guard+") ) ==> ";
		Exceptpost += "("+StateDeclarationPrefix+stateName+"=="+StateDeclarationPrefix+outTransition.to;
		Exceptpost += ") \n";
		signals.add(Exceptpost);
		
		exceptTermUsed = true;
	}	
	public void addEntryActions(String updatefunction, String[] updateParam){
		//add entry actions to the method if not already present
		
		boolean found=false;
		String string;
		String cmpString = updatefunction+"("+updateParam[0];
		for (int i=1 ; i<updateParam.length ; i++) cmpString += ", "+updateParam[i];
		cmpString += "); \n";
		Iterator it = entryActions.iterator();
		while (it.hasNext()){
			string = (String) it.next();
			if (cmpString.compareTo(string)==0) found=true;
		}
		if (!found) entryActions.add(cmpString);
	}
	public void addNormalExitActions(String updatefunction, String[] updateParam){
		//add exit action associated to normal terminaison
		
		boolean found=false;
		String string;
		String cmpString = updatefunction+"("+updateParam[0];
		for (int i=1 ; i<updateParam.length ; i++) cmpString += ", "+updateParam[i];
		cmpString += "); \n";
		Iterator it = normalExitActions.iterator();
		while (it.hasNext()){
			string = (String) it.next();
			if (cmpString.compareTo(string)==0) found=true;
		}
		if (!found) normalExitActions.add(cmpString);
	}
	public void addExceptExitActions(String updatefunction, String[] updateParam){
		//add exit action associated to exceptional terminaison
		
		boolean found=false;
		String string;
		String cmpString = updatefunction+"("+updateParam[0];
		for (int i=1 ; i<updateParam.length ; i++) cmpString += ", "+updateParam[i];
		cmpString += "); \n";
		Iterator it = exceptExitActions.iterator();
		while (it.hasNext()){
			string = (String) it.next();
			if (cmpString.compareTo(string)==0) found=true;
		}
		if (!found) exceptExitActions.add(cmpString);
		exceptTermUsed = true;
	}
	/*public void addState(String Prefix, String stateName ){
		//adds conditionally : a new dependency with a given property (if not already there)
		boolean found =false;
		String recordedString;
		Iterator it = propertyList.iterator();
		while (it.hasNext() && !found) {
			recordedString = (String) it.next();
			//if (Pattern.compile(PropertyClassName).matcher(recordedString).find() ){found= true;}
			if (PrefixedStateName.equals(recordedString)==true){found=true;}
		}
		if (found==false) {propertyList.add(PrefixedStateName);}	
	}	
	*/
	
	//Function finalising the generation of annotation for after a new property has been added
/*	public void addMethodEntryPoints(String stateName, LinkedList states){
		/*Once the whole property has been added, one must complete the annotation :
	 	While the automaton is stucked in states which are waiting for a specific method terminaision
	 	any method can be called, except the one already declared for this state with call ('!' in synchro):
	 	requires statements must allow these methods to be called. "mp.addMethodEntryPoints(StateName, states)" will do so  
	
		State state;
		String string;
		Iterator it1, it2 ; 

		
		if (terminaisonUsed == 0) return;//the terminaison of method is not used, no need to add states
		if (callUsed == 0) return; 	 	 //no requires statement has been inserted, nothing will be specified as precondition
		
		//otherwise, something should be inserted to complete the precondition
		it1 = states.iterator();
		while(it1.hasNext()){
			state = (State) it1.next();
			it2 = callStates.iterator();
			while (it2.hasNext()){
				string = (String) it2.next();
				if (string.compareTo(state.stateName)!=0) {
					string = (String) precondition.removeLast();
					string += "("+stateName+"=="+state.stateName+") \n";
					precondition.add(string);
				}
			}
		}
		
		
	}*/
	public void releaseAutomaton(String propClassName, String stateName, String stateUpdateFunction, 
			String[] entryUpdateParam,
			String[] exitUpdateParam ,
			String[] exitUpdateParamExcep){
		
		
		//here should be inserted the compulsary exit-actions needed 
		//at the end of the synthesis phase of each automaton.
		String string =  (String) precondition.getLast(); //inString used only for test
		if (string.compareTo("")!=0) precondition.add(new String("") );
		
		
		//a new variable (unmodified yet) is being added
		if (modifiable.compareTo("")!=0) modifiable += ", ";
		modifiable += propClassName+"."+stateName;
		
			
		
		/* Adding actions associated to automaton evolution */
		string = "set "+propClassName+"."+stateName+"="+propClassName+"."+stateUpdateFunction+"(";
		String entryAct = "" , nExitAct = "", eExitAct = "";
		//entry action string
		if (entryUpdateParam.length>0) entryAct += string + entryUpdateParam[0];
		for (int i=1 ; i<entryUpdateParam.length ; i++) entryAct += ", "+entryUpdateParam[i];
		entryAct += "); \n";
		// normal exit action
		if (exitUpdateParam.length>0) nExitAct += string + exitUpdateParam[0];
		for (int i=1 ; i<exitUpdateParam.length ; i++) nExitAct += ", "+exitUpdateParam[i];
		nExitAct += "); \n";
		// exceptional exit action
		if (exitUpdateParamExcep.length>0) eExitAct += string + exitUpdateParamExcep[0];
		for (int i=1 ; i<exitUpdateParamExcep.length ; i++) eExitAct += ", "+exitUpdateParamExcep[i];
		eExitAct += "); \n";
		
		
		entryActions.add(entryAct);
		normalExitActions.add(nExitAct);
		if (exceptTermUsed) exceptExitActions.add(eExitAct);
		exceptTermUsed = false;
	}
	
	
	/*Functions implementing the interfaces*/
	public int compareTo(Object obj){
		int i;
		MethodProperty mp;

		if (!(obj instanceof MethodProperty)) {throw new ClassCastException();} 
		mp=(MethodProperty)obj;
		i = this.ownerClass.compareTo(mp.ownerClass); /*System.out.println("cmp owner class="+i);*/
		if (i==0){i = this.classDefinition.compareTo(mp.classDefinition);/*System.out.println("cmp owner class def="+i);*/}
		if (i==0){i = this.methodName.compareTo(mp.methodName);/*System.out.println("cmp method="+i);*/}
		if (i==0){i = this.methodDefinition.compareTo(mp.methodDefinition);/*System.out.println("cmp method def="+i);*/}
		
		return i;
	}	

	
	
		
	/*
	 * 	Access functions  
	 * 
	 */
	public String getMethodName(){ return methodName;}
	public String getMethodDefinition() {return methodDefinition ;}
	public String getClassDefinition()  {return classDefinition ;}
	public String getOwnerClass(){ return ownerClass;}
	
	/*The below methods give a unique String representation of the annotation list fields 
	 	They implicitely define the way properties aggregated*/
	public String getPrecond()	{
		
		Iterator it = precondition.iterator();
		String annotation="";
		String string;	
		
		while (it.hasNext()){
			string = Pattern.compile("\n").matcher( (String)it.next() ).replaceAll("|| \n");
			if (string.compareTo("") != 0 ) {
				annotation += "/*@ requires "+string;
				annotation = annotation.substring(0, annotation.lastIndexOf("|| \n"));
				annotation +=" ; @*/ \n"; 
			}
		}
		return annotation;
	}
	public String getModifies() { 
		int i;
		if (modifiable.compareTo("")==0) return "";
		else return ("/*@ modifies "+modifiable+"; @*/ \n");
	}
	public String getNormalPostcond() { 
		
		Iterator it=postcondition.iterator();
		String annotation="";
		
		if (it.hasNext()){
			while (it.hasNext()){annotation += "/*@ ensures "+((String)it.next()).trim()+" ; @*/ \n"; }
			//annotation = annotation.substring(0, annotation.lastIndexOf(" \n"));
		}
		return annotation;
	}
	public String getExceptPostcond() { 
		
		Iterator it=signals.iterator();
		String annotation="";
		
		if (it.hasNext()){
			while(it.hasNext()){ annotation += "/*@ exsures "+((String)it.next()).trim()+" ; @*/ \n"; }
			//annotation = annotation.substring(0, annotation.lastIndexOf(" \n"));
		}
		return annotation;
	}
	public String getEntryActions(){
		
		Iterator it=entryActions.iterator();
		String annotation="";
		String string;
		
		if (it.hasNext()){
			annotation += "/*@ "+(String)it.next();
			while(it.hasNext()){ 
				annotation += (String)it.next(); 
			}
			annotation = annotation.trim()+" @*/ \n";
		}
		
		return annotation;
	
	}
	public String getNormalExitActions(){
		Iterator it=normalExitActions.iterator();
		String annotation="";
		
		if (it.hasNext()){
			annotation += "/*@ "+(String)it.next();
			while(it.hasNext()){ 
				annotation += (String)it.next(); 
			}
			annotation = annotation.trim()+" @*/ \n";
		}
		
		return annotation;
	}
	public String getExceptExitActions(){
		Iterator it=exceptExitActions.iterator();
		String annotation="";
		
		if (it.hasNext()){
			annotation += "/*@ "+(String)it.next();
			while(it.hasNext()){ 
				annotation += (String)it.next(); 
			}
			annotation = annotation.trim()+" @*/ \n";
		}
		
		return annotation;
	}
	
	
	//Display function
	public String toString(){
		String string = "";
	
		if (classDefinition != null) string += "Class Definition: "+classDefinition.trim();
		string += "\nClass Owner: "+ownerClass.trim();

		//print all the names of properties attached to this method
		
		//Iterator iter=propertyList.iterator() ;
		//if( iter.hasNext() ) string += "\nUsing properties: ";
		//while ( iter.hasNext() )  string+= (String)iter.next()+" ; " ;
		if (methodDefinition != null) string += "\nMethod Definition: "+methodDefinition.trim();
		string += "\nMethod: "+methodName.trim()+"\n";
		string += getPrecond().trim()+"\n";			//"Pre:------------\n"+
		string += getModifies().trim()+"\n";		//"Modifies:-------\n"+
		string += getNormalPostcond().trim()+"\n";	//"Post:-----------\n"+
		string += getExceptPostcond().trim()+"\n";	//"Signals:--------\n"+
		string += "Entry Actions:------------------\n"+getEntryActions().trim()+"\n";
		string += "Exit Actions (before return):---\n"+getNormalExitActions().trim()+"\n";
		string += "Exit Actions (before throw) :---\n"+getExceptExitActions().trim()+"\n";
		return string;
	}
	
	public static String[] getDotPropContent(LinkedList mpList){
		
		int i;
		String string = "";
		//String requires ;
		//String modifies ;
		//String ensures ;
		//String exsures ;
		MethodProperty mp;
		String currentClass = "";
		boolean firstTime = true;
		LinkedList tmpPropList = new LinkedList();
		
		//remove case where list is void
		if (mpList.size()==0) return new String[1];
		System.err.println("===============\nHere is the list of methods returned:");
		
		//list contains at least one element
		Collections.sort(mpList);
		for(i=mpList.size() ; i>0 ;i--){
			mp = (MethodProperty) mpList.get(i-1);	
			if (currentClass.compareTo(mp.getOwnerClass())!=0){
				//add to LinkedList
				if (!firstTime){
					string = string.replaceAll("(?m)^","\t");
					string = currentClass+"{\n\n"+string +"\n} \n";
					tmpPropList.add(string);
				}
				
				System.err.println("Change from "+currentClass+" to "+mp.getOwnerClass()+" class");
				
				//Build new string
				currentClass = mp.getOwnerClass();
				string = "";
				
			}
			
			string += mp.getPrecond();
			string += mp.getModifies();
			string += mp.getNormalPostcond();
			string += mp.getExceptPostcond();
			//forget entry/exit actions
			/*if (exsures.trim().compareTo("")!=0) { try{}catch{}finally{}... }*/
			string += mp.getMethodDefinition()+"; \n\n\n";
			
			firstTime = false;
			
		}  
		//add last
		string = string.replaceAll("(?m)^","\t");
		string = currentClass+"{\n\n"+string +"\n} \n";
		tmpPropList.add(string);
		
		System.err.println("===============\n -> There are "+tmpPropList.size()+" different classes");
		
		
		//Convert tmpPropList to string array
		//System.out.println("Length of list: "+tmpPropList.size());
		String[] PropList = new String[tmpPropList.size()];
		for(i=tmpPropList.size() ; i>0 ;i--) { PropList[i-1]=(String)tmpPropList.get(i-1);}
		
		return PropList;
	}
	
	public static String[] getUpdateActions(LinkedList mpList){
		
		int i;
		String string = "";
		String IActions ;
		String NOActions ;
		String EOActions ;
		//String exsures ;
		MethodProperty mp;
		String currentClass = "";
		boolean firstTime = true;
		LinkedList tmpPropList = new LinkedList();
		
		//remove case where list is void
		if (mpList.size()==0) return new String[1];
		
		//list contains at least one element
		Collections.sort(mpList);
		
		
		//Show out the mpList returned
		Iterator it = mpList.iterator();
		System.err.println("===============\nHere is the list of methods returned:");

		for(i=mpList.size() ; i>0 ;i--){
			
			mp = (MethodProperty) mpList.get(i-1);	
			if (currentClass.compareTo(mp.getOwnerClass())!=0){
				//add to LinkedList
				if (!firstTime){
					string = string.replaceAll("(?m)^","\t");
					string = currentClass+"{\n\n"+ string +"\n} \n";
					tmpPropList.add(string);
				}
				
				System.err.println("Change from "+currentClass+" to "+mp.getOwnerClass()+" class");
								
				//Build new string
				currentClass = mp.getOwnerClass();
				string = "";
			}
			
			System.err.println( " - "+((MethodProperty)mpList.get(i-1)).getMethodName() );
			
			string += mp.getMethodDefinition()+"{\n";
			string += "\tboolean __INTERNAL_TEST = false; \n";
			string += "\t/* Entry Actions */\n";
			if (mp.getEntryActions().trim().compareTo("")!=0) { 
				string += mp.getEntryActions().replaceAll("(?m)^","\t");
			}
			string += "\ttry{\n\t\t/*-- Method Body --*/\n";
			string += "\n\t\t/*--- End Body ---*/\n";
			string += "\t}\n";
			string += "\tcatch(Exception e){ \n";
			string += "\t\t__INTERNAL_TEST = true; \n";
			string += "\t\t/* Exceptional Exit Actions */\n";
			if (mp.getExceptExitActions().trim().compareTo("")!=0) { 
				string += mp.getExceptExitActions().replaceAll("^","\t\t");
				string += "\t\tthrow e;\n";
			}
			string += "\t} \n";
			if (mp.getNormalExitActions().trim().compareTo("")!=0) { 
				string += "\tfinally{ \n";
				string += "\t\t/* Normal Exit Actions */\n";
				string += "\t\tif (!__INTERNAL_TEST ){\n";
				string += mp.getNormalExitActions().replaceAll("(?m)^","\t\t\t");
				string += "\t\t}\n";
				string += "\t}\n";
			}
			string += "}\n\n";
			
			firstTime = false;
			
		}  
		//add last
		string = string.replaceAll("(?m)^","\t");
		string = currentClass+"{\n\n"+ string +"\n} \n";
		tmpPropList.add(string);
		
		System.err.println("===============\n -> There are "+tmpPropList.size()+" different classes");
		
		//Convert tmpPropList to string array
		//System.out.println("Length of list: "+tmpPropList.size());
		String[] PropList = new String[tmpPropList.size()];
		for(i=tmpPropList.size() ; i>0 ;i--) { PropList[i-1]=(String)tmpPropList.get(i-1);}
		

		
		return PropList;
	}
	
}