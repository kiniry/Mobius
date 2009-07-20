/*
 * Created on Mar 11, 2005
 *
 * TODO To change the template for this generated file go to
 * Window - Preferences - Java - Code Style - Code Templates
 */

/**
 * @author tdupont
 * 
 * TODO To change the template for this generated type comment go to Window -
 * Preferences - Java - Code Style - Code Templates
 */



import java.util.LinkedList;
import java.util.regex.*;
import java.util.Iterator;
import java.lang.String;
import org.w3c.dom.Node;


public class Outils {
	private static Outils instance = new Outils();

	public static Outils outilsFactory() {
		return instance;
	}

	//the strings below are defined the position of parameters in the method instanciation (in UPPAAL)
	//if new field are introduced be sure to keep at least the already existing names (e.g. "Call")
	private final String[] synchroTypeString = { "Call", "Normal Terminaison", "Except Terminaison" };
	public String synchroTypeToString(int i){return synchroTypeString[i];}
	
	
	
	/** General purpose function **/
	//Remove comment C-type comment keeping annotation '//@'
	//(works for multilines)
	public String removeComment(String string) {
		
		int length=1;
		String[] fragments;
		String tmp;
		Matcher matcher;
		
		// Setting patterns for comment removal
		//Pattern.DOTALL <=> (?s)
		//Pattern.MULTILINE <=> (?m)
		//Pattern.CASE_INSENSITIVE <=> (?i)
		Pattern Annotation 	= Pattern.compile("//@.*");
		Pattern Comment1 = Pattern.compile("//[^@].*");
		Pattern Comment2 = Pattern.compile("(?m)(?i)(?s)/\\*.*?\\*/");
			
		//Remove Multiline Comments
		matcher = Comment2.matcher(string);
		while (matcher.find()) {
		//Concatenate splits part
			string = string.substring(0, matcher.start() ) + string.substring(matcher.end() );
			matcher.reset(string);
		}
		
		//Remove Line comments
		matcher = Comment1.matcher(string);
		while ( matcher.find() ) {
			string = string.substring(0, matcher.start() ) + string.substring(matcher.end() );
			matcher.reset(string);
		}

		
		//Remove finally empty lines
		tmp = "";
		matcher = Pattern.compile(".*\\S+.*").matcher(string);
		while (matcher.find() ){tmp += matcher.group()+"\n";	}
				
		return tmp;
	}

	//Extract from a comments-free declaration the variable and annotation
	//(relies on the fact that removeComment function had been applied previously)
	private LinkedList extractVariablesDef( String string){
		
		int count;
		LinkedList list= new LinkedList();
		Variables var;
		String tmp, name = "" , type = "" , annotation = "", initValue ="";
		String namePattern;
		
		//Pattern Definition 
		Matcher definitionMatcher = Pattern.compile("^\\s*([^;]+);(.*)").matcher(string);
		Matcher annotationMatcher = Pattern.compile("^\\s*(//@.*)").matcher(string);
		Matcher voidMatcher = Pattern.compile("\\S+").matcher(string); 	
		namePattern = "(\\s+|,)\\s*(\\w+)\\s*(:=(\\s*[^,]+))?" ;
		Matcher varMatcher = Pattern.compile("((int)|(bool)|((broadcast\\s+)?chan))"+namePattern).matcher("");
		Matcher nameMatcher = Pattern.compile(namePattern).matcher("");// original pattern is : "(\\s+|,)\\s*(\\w+)(\\s*:=(\\s*[^,]+))?" 

		
		//System.out.println("Extract Variables Definition");	
		
		while (voidMatcher.find()){
			//System.out.println("current string is: " + string);
					
			if ( annotationMatcher.find() ){
				//if line begins by an annotation, store it for next
				annotation += annotationMatcher.group(1) + "\n";	
				string = string.substring(annotationMatcher.end());
				
			}
			else {
				//else line should contain a variable definition
				if (definitionMatcher.find()){
					string = string.substring(definitionMatcher.end());
					count = definitionMatcher.groupCount();
					name = definitionMatcher.group(1); //contains temporaly the definition
					if ( count == 2){ 
						//something is remaining on the line
						//store in appropriate variable if annotation 
						//store in the string for latter analysis if not
						tmp = definitionMatcher.group(2);
						annotationMatcher.reset(tmp);
						if (annotationMatcher.find() ) {annotation += annotationMatcher.group();}
						else { string = tmp + string;}	
					}
					
					//extraction of data in the definition
					varMatcher.reset(name);
					if (varMatcher.find()){
						type = varMatcher.group(1);				//extraction of the type
						name = name.substring(type.length()); 	//remove type information
						//System.err.println("extracted Type is: "+type+"\nnames will be extracted from: "+name);
						nameMatcher.reset(name);				//initialize the name pattern
						if (!(nameMatcher.find())) return null;
						do { //there is a definition on the line
							if (nameMatcher.groupCount()==4) { initValue = nameMatcher.group(4);}
							name = nameMatcher.group(2);
							
							//set Variable
							var = new Variables();
							var.name = name;
							var.type = type;
							if (initValue != null) { 
								if (initValue.trim().compareTo("")!=0) var.initValue= initValue;} 
							if (annotation != null) {
								if (annotation.trim().compareTo("")!=0) var.annotation=annotation;}

							
							//System.err.println("Var extracted is: "+var);
							
							//add variable to list
							list.add(var);			
							
						
						}while (nameMatcher.find());
					
					}
					annotation = ""; //compulsary reset 
				}
				else { 
					//remove the line to avoid infinite loop
					string =  string.substring( string.indexOf('\n') + 1);
					
					//May rather throw an exception
					System.err.println("Err : line should contain a variable definition");}	
			}
			
			//string is being emptied, at each round
			annotationMatcher.reset(string);		
			definitionMatcher.reset(string);
			voidMatcher.reset(string);
		}
		
		return list;
	}
	
	//Given a declaration node, the function returns the 
	//declared list of variable
	public LinkedList extractDeclaration(Node node){
		
		LinkedList list;
		Node child;
		String name, type, value = "";
		Variables var;

		/********  Verifications  ********/
		//if node is a contains a declaration
		if (!(Name(node).toLowerCase().compareTo("declaration") == 0
				&& Type(node).toLowerCase().compareTo("element") == 0)) {System.out.println("node contains no declaration");return null;}
		//The Declaration must only contain 1 Text element
		if (childCount(node) == 0 ) {System.out.println("node has no child ... ?");return null;}
		if (childCount(node) > 1 ) {System.out.println("Declaration contains several text elements");displayFrom(0,node);return null;}
		child = child(node, 0);
		//Verify the type of the child 
		if (Type(child).toLowerCase().compareTo("text") != 0) {System.out.println("child type is not of text type");return null;}
		/*********************************/
		
		//System.out.println("Extraction of declaration is begining");
		
		//get value to proceed
		value = Value(child);
		//Remove comment included in the declaration
		value = this.removeComment(value);
		//Extract variables
		list = extractVariablesDef(value);
		//display
		//displayList(list);

		return list;
	}
	public LinkedList extractParameters(Node node){
		
		Iterator it;
		Variables var;
		LinkedList list ; //= new LinkedList();
		Node child;
		String value;

		/*********Verification**************/
		//if node is a contains a declaration
		if (!(Name(node).toLowerCase().compareTo("parameter") == 0
				&& Type(node).toLowerCase().compareTo("element") == 0)) return null;
		//The Declaration must only contain 1 Text element
		if (childCount(node) != 1 ) return null;
		child = child(node, 0);
		//Verify the type of the child 
		if (Type(child).toLowerCase().compareTo("text") != 0) return null;
		/***********************************/
		

		//get the value
		value = Value(child);
		//remove the comments 
		value = removeComment(value);
		//prepare data for processing
		if (value.trim().compareTo("") !=0) value =  value.trim() +";";
		//extract variables
		list = extractVariablesDef(value);
		//display
		//displayList(list);
		
		return list;//*/
	}
	//be careful the current function has a slightly different behavior compared to the other one
	//it is intended to be used in the instantiation section
	public LinkedList extractParameters(String string){
		
		Iterator it;
		Variables var;
		LinkedList list = new LinkedList();
		//remove Comments but there should not be any remaining one
		string = removeComment(string);

		//prepare data for processing
		if (string.trim().compareTo("") !=0) string = "chan "+ string.trim() +";"; //a type is artifically introduced
		//extract variables
		list = extractVariablesDef(string);
		it = list.iterator();
		while (it.hasNext()){var= (Variables)it.next();var.type="";}
		
		return list;
	}
	public LinkedList extractInstances(Node node, LinkedList propertiesModel){
		
		Outils o = Outils.outilsFactory();
		LinkedList properties;		//list of the properties effectively instanciated
		LinkedList methods;			//list of the methodProperty instantiated
		LinkedList paramLinks;		//list of the links between methods and properties instantiated
		Iterator it;
		
		Node child;
		String value, className ="", instanceName="", classDefinition="", methodDefinition="";
		String annotation="", instanceParam, objectInstantiated;
		String[] tmp;
		MethodProperty method;
		Property property;

		/********  Verifications  ********/
		//if node is a contains a instanciation
		if (!(o.Name(node).toLowerCase().compareTo("instantiation") == 0
				&& o.Type(node).toLowerCase().compareTo("element") == 0)) return null;
		//The Declaration must only contain 1 Text element
		if (o.childCount(node) != 1 ) return null;
		child = o.child(node, 0);
		//Verify the type of the child 
		if (o.Type(child).toLowerCase().compareTo("text") != 0) return null;
		/********************************/

		properties = new LinkedList(); //list of Properties containing the properties being instanciated
		methods    = new LinkedList(); //list of MethodProperty containing the methods being instanciated
		paramLinks = new LinkedList(); //list of ParamLink linking parameters of intantiated properties and methods
		value = o.Value(child);
		value = o.removeComment(value);
		
		//Define general pattern for instances
		Matcher instanceMatcher = Pattern.compile("^\\s*(\\w+)\\s*:=\\s*(\\w+)\\s*\\((.*)\\).*").matcher(value);
		Matcher annotationMatcher = Pattern.compile("^\\s*//@(.*)").matcher(value);
		Matcher voidMatcher = Pattern.compile("\\S+").matcher(value); 
		//Matcher methodMatcher = Pattern.compile(".*\\s+(\\w+)\\s*\\((.*)\\)(.*)").matcher("");
		Matcher methodMatcher = Pattern.compile(".*\\s*(\\w+)\\s*\\((.*)\\)(.*)").matcher("");
		Matcher matcher;

		System.err.println("\t\t\tBegin matching");
		
		while (voidMatcher.find()){	//As long as there are instance to extract
			
			//if annotation : extract class and methode definition
			if (annotationMatcher.find()){
				annotation = annotationMatcher.group(1);
				value = value.substring(annotationMatcher.end());
				//try to decode annotation
				methodMatcher.reset(annotation);
				tmp = annotation.split("(?i)class");
				if (tmp.length == 2){ 
					// it is a class definition
					System.err.println("found class definition class "+tmp[1]);
					classDefinition = annotation;
					matcher= Pattern.compile("^\\s*(\\w+)").matcher(tmp[1]);
					if (matcher.find()) { className= matcher.group(1);}
					/*System.out.println("Found class def in annoatation: "+annotation+
							"("+className+")");//*/
				}
				else if (methodMatcher.find()){
					//it is a method definition
					System.err.println("found method definition "+annotation);
					methodDefinition = annotation;
					instanceName = methodMatcher.group(1);
					/*System.out.println("Found method def in annoatation: "+annotation+
							"("+instanceName+")");//*/
				}
			}
			//If it is an instance
			else if (instanceMatcher.find()){ 
				value = value.substring(instanceMatcher.end());
				instanceName = instanceMatcher.group(1);
				objectInstantiated = instanceMatcher.group(2);
				instanceParam = instanceMatcher.group(3);
				
				//if it is a method that is being instanciated (identified by the "MethodBehavior" key word) 
				if (objectInstantiated.compareToIgnoreCase("methodbehavior")==0){ 
					System.out.println("Found method "+instanceName+" belonging to "+className + 
							" with definition "+methodDefinition);
					
					method = new MethodProperty(className, instanceName);
					if (methodDefinition.compareTo("")!=0){
						method.setMethodDefinition(methodDefinition);}
					if (classDefinition.compareTo("")!=0){
						method.setClassDefinition(classDefinition);}
					
					methodDefinition = ""; //a method is valid for 1 function at most
					
					//System.out.println(method.toString());
					if (! methods.add(method)) {System.err.println("error while adding new instance method");return null;}
					//System.err.println("editParamLinkList called for "+method.getMethodName());
					paramLinks = editParamLinkList(paramLinks, instanceParam, method);					
				}
				//then it is a property instanciation;
				else{ 					
					
					methodDefinition = "";
					
					//find the property
					it=propertiesModel.iterator();
					property = null;
					while(it.hasNext() && property==null){
						property=(Property)it.next();
						if (property.propertyName.compareTo(objectInstantiated)==0) 
						{//make a clone of the model property
							try{
								//System.out.println("Instanciating property "+property.getPropClassName());
								property = (Property)property.clone();
							}catch(Exception e){System.err.println("error while instanciating(cloning) a property");return null;}
							//System.err.println("property successfully instanciated");
						}
						else property = null;
					}
					//register it
					if (!properties.add(property)) {System.err.println("error while adding a property");return null;}
					
					//rename the property
					property.propertyName = instanceName;
					
					//take the parameters into account
					LinkedList newParamList;
					newParamList = extractParameters(instanceParam);
					property.renameParameters(newParamList);
					//System.err.println(property);
				}
				
			}
			//Neither an instance nor an annotation
			else { 
				//remove the line to avoid infinite loop
				//May rather throw an exception
				value =  value.substring( value.indexOf('\n') + 1);
				System.err.println("Err : line should contain a variable definition");
				//return false;
			}	
			
			//reset matchers for next round
			instanceMatcher.reset(value);
			annotationMatcher.reset(value);
			voidMatcher.reset(value);
			
		}	

		//Associate every Transition of every property with the MethodProperty 
		//System.out.println("Linking parameters to methods");
		if (! linkMethodToSynchro(properties,paramLinks)) {System.err.println("error while linking methods to synchro fields of transition");return null;};
				
		System.err.println("\t\t\tEnd Matching");
		
		
		return properties;
	}
	public boolean extractSystem(Node node){return false;}
	
	private class ParamLink implements Comparable, Cloneable{
		
		//fields
		public MethodProperty methodProperty;
		public int type; //position in the parameter list: i.e. exceptional behavior ...
		public Variables paramName;
		
		//functions
		public String typeToString(){return synchroTypeToString(type);}
		protected Object clone()  throws CloneNotSupportedException
		{ 
			return super.clone();
		}
		public ParamLink(Variables parameterName) {
			paramName = parameterName;
			methodProperty = null;
			//property = null;
		}
		public String paramName(){return paramName.name;}
		public int compareTo(Object obj){
			int i;
			ParamLink link;
			
			if(!(obj instanceof ParamLink)) throw new ClassCastException();
			link = (ParamLink)obj;
			i = this.paramName.compareTo(link.paramName);
			return i;
			
		}
		
	}
	
	
	/** TODO modify the function such as when a property is added, it considers the 
	 * already existing function and does not create an new method property
	 * 
	 * 	Alternative is to add to MethodProperty a merge function that could merge together
	 * 	 2 methodProperty if they are discribing the same method (same class, function, and declaration)
	 * 
	 * 	Another way would be to postpone this problem to the function annotating effectively the function,
	 *   which will be developed latter on.
	 * 
	 *  */
	//takes as input a list of ParamLink element, a string representing parameters declaration in instance,
	//and the object newly created, namely a MethodProperty or a Property
	//Returns the refreshed list, taking into account the new obj created
	/* 1 - 
	 	! This method can create ParamLink that would never link method and parameter, in this case
	 	! ParamLink would just be related a param to a global variable with no relation to a method
	   2 -
	   	! A method parameter could be linked with several properties = Several properties can
	   	! target a same method
	*/
	private LinkedList editParamLinkList(LinkedList list, String param, MethodProperty obj){
		
		ParamLink paramLink;
		Property prop;
		Variables var;
		LinkedList newParamList;
		Iterator it1, it2;
		int i=0;	
		
		
		//extract parameters out of the string
		newParamList = extractParameters(param);
		
		//foreach of the parameters
		it1 = newParamList.iterator();
		while (it1.hasNext()){
			var = (Variables)it1.next();
							
			//adding unconditionnaly the new paramLink
			paramLink = new ParamLink(var);
			if(!(list.add(paramLink))) {System.err.println("error while linking instances");return list;}
			
			//add new information, and new ParamLink by default
			paramLink.methodProperty = (MethodProperty)obj;
			paramLink.type = i;  //set the position of the parameter in the list. 
			//System.err.println("Creating "+(i+1)+"eme parameter (Called "+paramLink.methodProperty.getMethodName()+")");
			i++;
		}

		return list;
	}		
	
	//The goal of this function is to set the MethodProperty field of each transition
	//with the function it synchronizes to (method name is the one declared in the synchro field of the transition) 
	private boolean linkMethodToSynchro(LinkedList properties, LinkedList paramLinks){
		
		Iterator it1, it2, it3 ;
		Property prop;
		Transition transition;
		ParamLink paramLink;
		
		int i=0;
		
		it1 = properties.iterator();
		//foreach paramLink
		while (it1.hasNext()){
			prop =(Property)it1.next();
	
			//foreach transition
			it2=prop.edges.iterator();
			while (it2.hasNext()){
				transition = (Transition)it2.next(); 

				it3 = paramLinks.iterator();
				paramLink = null;
				while (it3.hasNext() && paramLink==null){
					paramLink = (ParamLink)it3.next();
					//System.err.println(i+"eme tour:"+paramLink.paramName.name);
					if (paramLink.paramName.name.compareTo(transition.synchro)!= 0 ) paramLink = null;
				}
				if (paramLink == null) {System.err.println("Impossible to link transition "+transition+
						"(of prop: "+prop.propertyName+")");
						return false;
				}		
			
				i++;
				
				//insert reference to methodProperty
				transition.mp = paramLink.methodProperty;	//remains uninitialized till the instanciation had been processed
				transition.synchroType = paramLink.type;
				//System.out.println(transition.toString());
			}
		}
		
		return true;
	}
	
	
	
	
	
	
	/** 
	 *  
	 * General XML functions dedicated to UPPAAL Automata 
	 * 
	 * 
	 * **/
	// XML ELEMENT TYPE DEFINITION, which is implicitely used by the parser
	static final String[] typeName = { "none", "Element", "Attr", "Text", "CDATA", "EntityRef", "Entity", "ProcInstr", 
			"Comment","Document", "DocType", "DocFragment", "Notation", };

	static final int ELEMENT_TYPE = 1;
	static final int ATTR_TYPE = 2;
	static final int TEXT_TYPE = 3;
	static final int CDATA_TYPE = 4;
	static final int ENTITYREF_TYPE = 5;
	static final int ENTITY_TYPE = 6;
	static final int PROCINSTR_TYPE = 7;
	static final int COMMENT_TYPE = 8;
	static final int DOCUMENT_TYPE = 9;
	static final int DOCTYPE_TYPE = 10;
	static final int DOCFRAG_TYPE = 11;
	static final int NOTATION_TYPE = 12;

	//FUNCTION TO BROWSE THE XML DOM-TREE
	//return the number of chid of a particular node
	public int childCount(Node node) {
		return node.getChildNodes().getLength();
	}
	//return the child node, referenced at 'index'
	public Node child(Node node, int index) {
		return node.getChildNodes().item(index);
	}
	//return the parent node
	public Node parent(Node node) {
		return node.getParentNode();
	}

	
	//FUNCTIONS RETURNING XML-NODE properties
	//return the name of the node
	public String Name(Node node) {
		return node.getNodeName();
	}
	//return the type of the node
	public String Type(Node node) {
		return typeName[node.getNodeType()];
	}
	//return the value of the node
	public String Value(Node node) {
		return node.getNodeValue();
	}


	//FUNCTION DEDICATED TO ATTRIBUTES 
	//Attribute management compusary 
	//   (ex : source name of transition contained in attrib )
	public boolean hasAttributes(Node node) {
		if (attributeCount(node) <= 0) {return false;}
		return true;
	}
	//return the number of attributes
	public int attributeCount(Node node) {
		if (this.Type(node) != "Element") { return -1;}
		return node.getAttributes().getLength();
	}
	//return a standard node representing the ith attribute
	public Node Attribute(Node node, int index) {
		return node.getAttributes().item(index);
	}
	
	
	/****************  Affichage primitif dans Terminal  ******************/
	//Below functions display DOM tree
	public void displayFrom (int level , Node node){
		
		Outils o = Outils.outilsFactory();
		String indent = "";
		Node child ;	
		
		displayNodeInformation (level, node);
		
		
		level ++;
		for (int i=0 ; i<o.childCount(node) ; i++){
			child = o.child(node,i);
			displayFrom(level, child);
		}
		
	}
	public void displayNodeInformation (int level, Node node){
		
		Outils o = Outils.outilsFactory();
		String indent = "";
		Node child ;	
		
		for (int i=0 ; i< level ; i++) {indent += "--";}
		System.err.println( indent + "Type :  "+ o.Type(node) );
		System.err.println( indent + "Name :  "+ o.Name(node)  );	
		System.err.println( indent + "Value: " +o.Value( node) );
	
		//display attributes here
		for (int i=0 ; i < o.attributeCount(node) ; i++ ){
			child = o.Attribute(node, i);
			System.err.println( indent + "Attrib. Type:  "+ o.Type(child) );
			System.err.println( indent + "Attrib. Name : "+ o.Name(child)  );	
			System.err.println( indent + "Attrib. Value: " +o.Value(child) );			
		}
		
	}
	public void displayList(LinkedList list){
		
		for( Iterator iter = list.iterator(); iter.hasNext(); System.out.println(iter.next()) );
	
	}
	

}