/**
 * @title "Semantic Property Plugin Package"
 * @description "Class that represents,checks and generates a regexp for a semantic property."
 * @author  Eoin O'Connor
 * @copyright ""
 * @license "Public Domain."
 * @version "$Id: 01-07-2010 $"
 */

package ie.ucd.semantic_properties_plugin.file_checker;

import java.util.ArrayList;
import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.Map;
import java.util.Set;
import java.util.regex.Matcher;
import java.util.regex.Pattern;


import semantic_properties_plugin.custom_objects.MyObject;


/**
 * <p> A class representing a semantic property that consists of
 * format,name,scope,description and a regular expression structure.</p>
 *
 * @see    RegExpStruct
 * @version "$Id: 01-07-2010 $"
 * @author  Eoin O'Connor
 **/

public class Property {

	
	// Attributes

	  /**
	   * <p> definition of what makes an acceptable property  using regular expressions for
	   *  name,scope,description and the different format possibilities </p>
	   */
	final static String prop_Scope = "(files|modules|features|variables|all|special)";
	final static String prop_Description = ".*";
	final static String prop_format_String = "(\\w*)";
	final static String prop_format_CustomObject = "(\\w+=(\\w|[0-9]|\\.)+)";
	final static String prop_format_Special = "((choice\\s*\\((\\w+)\\)\\s*)|choice|optional)";	
	final static String prop_Name = "\\s*\\w+\\s*";

	 /**
	   * <p>  list of property attributes </p>
	   */
	public static ArrayList<Object> format;
	public static ArrayList<String> scope;
	public static String description;
	public static String name;
	private RegExpStruct reg;
	
	// Public Methods

	  /**
	   * default constructor that uses default values 
	   */


	public Property() {
		format = new ArrayList<Object>();
		scope = new ArrayList<String>();
		description = new String();
		name = new String();
	  	reg= new RegExpStruct();

	}
	/**
	   * default constructor that uses linkedHashMap usually from snakeyaml to make property
	   * @param linkedHashMap the linkedhashMap that snakeyaml has produced
	   */

	public Property(LinkedHashMap<String, ?> linkedHashMap){
		
			if(!checkValidity(linkedHashMap)){
				System.out.println("linkedHashMap entery "+linkedHashMap+" does not represent a valid property not valid");
				System.exit(2);
			}
			else{
				name=(String)linkedHashMap.get("name");
				format=(ArrayList<Object>)linkedHashMap.get("format");
				description=(String)linkedHashMap.get("description");
				scope=(ArrayList<String>)linkedHashMap.get("scope");		  
				reg= generateRegExp();
			}
					
			  
	}
	/**
	 * Gets the regular expression for this property
	 * @return a RegExpStruct representation of this property
	 */

	public RegExpStruct getReg() {
		return reg;
	}

	public void setReg(RegExpStruct reg) {
		this.reg = reg;
	}
	/**
	 * checks prop for validity as defined by the strings at the beginning of this file
	 * @param newProp linkedHashMap that contains potential property as parsed by snakeyaml
	 * @return true when the property is a valid representation
	 */
	public boolean checkValidity(LinkedHashMap<String, ?> newProp) {



		// check name
		Pattern namePattern = Pattern.compile(prop_Name);

		Matcher nameMatcher = namePattern.matcher((String)newProp.get("name"));
		if (!nameMatcher.matches()) {
			System.out.println(" name value is invalid @" + name);
			return false;
		}

		// check scopes
		Pattern scopePattern = Pattern.compile(prop_Scope,
				Pattern.CASE_INSENSITIVE);
		ArrayList<String> scopes=(ArrayList<String>)newProp.get("scope");
		for (String scopeValue : scopes) {
			Matcher scopeMatcher = scopePattern.matcher(scopeValue);
			if (!scopeMatcher.matches()) {
				System.out.println(name + " scope value is invalid @"+ scopeValue);
				return false;
			}
		}

		// check Description
		Pattern descriptionPattern = Pattern.compile(prop_Description,
				Pattern.DOTALL);
		Matcher descriptionMatcher = descriptionPattern.matcher((String)newProp.get("description"));
		if (!descriptionMatcher.matches()) {
			System.out.println("The  properties description is invalid @"
					+ description);
			return false;
		}

		// check format with recursive method
		return checkFormatValidity((ArrayList<Object>)newProp.get("format"));

	}
	/**
	 * recursive method to be called by on any object to check if it is valid format object
	 * @param formatValue Object that may be 
	 * @return true when valid format object
	 */

	private boolean checkFormatValidity(Object formatValue) {

		// case for String
		if (formatValue instanceof String) {
			//check if its valid sting
			Pattern formatPattern = Pattern.compile(prop_format_String);
			Matcher nameMatcher = formatPattern.matcher((String) formatValue);
			if (!nameMatcher.matches()) {
				System.out.println("instance of string name value is invalid @" + formatValue);
				return false;
			}
		}
		// case for list
		else if (formatValue instanceof ArrayList<?>) {
			// check validity of all objects in list
			for (Object optionalNameValue : (ArrayList<?>) formatValue) {
				if(!checkFormatValidity(optionalNameValue)){
					System.out.println(optionalNameValue+"in arraylist"+"formatValue"+" is not valid");
					return false;
				}

			}

		}
		// case for linkedhashmap
		else if (formatValue instanceof LinkedHashMap<?, ?>) {
			// checks if it is an instance of optional:,choice:, or choice (op): and returns false otherwise
			
			Pattern formatPattern = Pattern.compile(prop_format_Special);			
			LinkedHashMap<String, ?> r = (LinkedHashMap<String, ?>) formatValue;
			//loop through all keys
			Set<String> keys=r.keySet();
			for(String s:keys){
				Matcher nameMatcher = formatPattern.matcher(s);
				if (nameMatcher.matches()){
					if(!checkFormatValidity(r.get(s))){
						System.out.println("option "+s+"has invalid paramters at @"+r.get(s));
						return false;
					}
				}
				else{
					System.out.println(" special value(eg:choice,optional) is invalid @" + s);
					return false;
				}
			}		
		}
		//case for custom objects
		else if (formatValue instanceof MyObject) {
			
			Pattern formatPattern = Pattern.compile(prop_format_CustomObject);
			Matcher nameMatcher = formatPattern.matcher(((MyObject)formatValue).toString());
			if (!nameMatcher.matches()) {
				System.out.println(" customObject value is invalid @ " + formatValue);
				return false;
			}
		}
		// case for Unrecognized object
		else {
			System.out
					.println("Should not have got here in name check, reason @ "
							+ formatValue);
			return false;
		}
		//returns true if object was recognized and didn't already fail
		return true;

	}

	/**
	 * recursive method to build regexp for property
	 * @return regexp representation of property 
	 */

	public static RegExpStruct generateRegExp() {
		RegExpStruct returnRegEx = generateRegExp(format);
		String start=name+"[\\s+]";
		String end=returnRegEx.getExp();
		start+=end;
		returnRegEx.setExp(start);
		return returnRegEx;
	}
	/**
	 * recursive method to build regexp for an object
	 * @param object to turn into regexp
	 * @return regexp representation of object 
	 */

	public static RegExpStruct generateRegExp(Object ob) {
		String space="[\\s+]";

		//when arraylist
		if (ob instanceof ArrayList<?>) {

			
			ArrayList<?> list = (ArrayList<?>) ob;
			
			ArrayList<RegExpStruct> rlist= new ArrayList<RegExpStruct>();
				
			//loop through all objects in list and generate regexp for each and add them to list
			for (Object obin : list) {
				RegExpStruct temp = generateRegExp(obin);
				rlist.add(temp);
			}
			
			//concat regular expressions
			String exp="";
			LinkedHashMap<String, Integer> gorup=new LinkedHashMap<String, Integer>(); 
			int numOfGroups=0;
			
			for (RegExpStruct o : rlist) {	
				exp+=o.getExp()+space;
				//concat map
				int mapEntriesAdded=0;
				//iterate through the groups in each object and correct mapping
				Iterator<?> it = o.getGroups().entrySet().iterator();
				while (it.hasNext()) {
					Map.Entry pairs = (Map.Entry) it.next();
					int i = (Integer) pairs.getValue();
					pairs.setValue(numOfGroups+ i);
					mapEntriesAdded++;
				}
				numOfGroups+=o.getNumberOfGroups();
				//add corrected groups to new list
				gorup.putAll(o.getGroups());
				//numOfGroups+=mapEntriesAdded;
				
				
			}
			//get rid of extra space
			exp=exp.substring(0,exp.length()-space.length());
			RegExpStruct concat= new RegExpStruct(exp,gorup,numOfGroups);
			return concat;
			
			
		}
		// if map
		if (ob instanceof LinkedHashMap<?, ?>) {
			RegExpStruct concatRegExp = new RegExpStruct();
			
			LinkedHashMap<String, ?> all = (LinkedHashMap<String, ?>) ob;
			
			
			// choice:(name) capturing case
			Set<String> keys=all.keySet();
			for(String s:keys){
				String check="choice\\s*\\((\\w+)\\)\\s*";
				Pattern checkPattern = Pattern.compile(check);
				Matcher checkMatcher = checkPattern.matcher(s);
				if (!checkMatcher.matches()) {
				   //if not special case exit
					break;
				}
				
				//get list of choices 
				ArrayList<?> choices=(ArrayList<?>)all.get(s);
				
				//find largest group and get list of reg exp
				ArrayList<RegExpStruct> rlist= new ArrayList<RegExpStruct>();
				int largestGroup=0;
				for (Object obin : choices) {
					RegExpStruct temp = generateRegExp(obin);
					rlist.add(temp);
					int numberOfGroups=temp.getNumberOfGroups();
					if(numberOfGroups>=largestGroup){
						largestGroup=numberOfGroups;
					}
				}
				
				//concat regular expressions, map & 
				String exp="(";
				LinkedHashMap<String, Integer> newMap=new LinkedHashMap<String, Integer>();
				newMap.put(checkMatcher.group(1), 1);
				int numOfGroups=0;
				for (RegExpStruct itemInList : rlist) {	
					exp+=itemInList.getExp();
					for(int i=itemInList.getNumberOfGroups();i<largestGroup;i++){
						exp+="()";
					}
					exp+="|";
					//concat map
					Iterator<?> it = itemInList.getGroups().entrySet().iterator();
					while (it.hasNext()) {
						Map.Entry pairs = (Map.Entry) it.next();
						int i = (Integer) pairs.getValue();
						pairs.setValue(1+ i);
					}
					//add corrected groups to new list
					newMap.putAll(itemInList.getGroups());
							
				}
				exp=exp.substring(0,exp.length()-1);
				exp+=")";
				RegExpStruct concat= new RegExpStruct(exp,newMap,largestGroup+1);
				return concat;
				
			}
			//choice: case
			if(all.containsKey("choice")){
				//get list of choices 
				ArrayList<?> choices=(ArrayList<?>)all.get("choice");
				
				//find largest group and get list of reg exp
				ArrayList<RegExpStruct> rlist= new ArrayList<RegExpStruct>();
				int largestGroup=0;
				for (Object obin : choices) {
					RegExpStruct temp = generateRegExp(obin);
					rlist.add(temp);
					int numberOfGroups=temp.getNumberOfGroups();
					if(numberOfGroups>=largestGroup){
						largestGroup=numberOfGroups;
					}
				}
				
				//concat regular expressions, map & 
				String exp="(?:";
				LinkedHashMap<String, Integer> newMap=new LinkedHashMap<String, Integer>(); 
				int numOfGroups=0;
				for (RegExpStruct itemInList : rlist) {	
					exp+=itemInList.getExp();
					for(int i=itemInList.getNumberOfGroups();i<largestGroup;i++){
						exp+="()";
					}
					exp+="|";
					//concat map
					newMap.putAll(itemInList.getGroups());
							
				}
				exp=exp.substring(0,exp.length()-1);
				exp+=")";
				RegExpStruct concat= new RegExpStruct(exp,newMap,largestGroup);
				return concat;

				
				
				
			}
			// optional case
			if(all.containsKey("optional")){
				Object optionOb=all.get("optional");
				RegExpStruct optionReg =generateRegExp(optionOb);
				
				String ex="(?:"+ optionReg.getExp()+")?";					
				LinkedHashMap<String, Integer> optionMap = new LinkedHashMap<String, Integer>();
	//			optionMap.put(optionReg.getExp(), 1);

				return new RegExpStruct(ex, optionMap, 0);
							
			}			
			return concatRegExp;

		}
		//   if string
		if (ob instanceof String) {

			return new RegExpStruct((String) ob,
					new LinkedHashMap<String, Integer>(), 0);

		}
		// custom objects
		if (ob instanceof MyObject) {
			MyObject thisOb = (MyObject) ob;
			LinkedHashMap<String, Integer> objectMap = new LinkedHashMap<String, Integer>();
			objectMap.put(thisOb.getId(), 1);

			return new RegExpStruct(  thisOb.getReg(), objectMap, 1);

		}
		else{
			return new RegExpStruct(
					"unexpected type encountered when generating RegExp in Propery.class"
							+ ob, new LinkedHashMap<String, Integer>(), 0);

		}
		
	}

	public static String getName() {
		return name;
	}

	public static void setName(String name) {
		Property.name = name;
	}

	public static ArrayList<String> getScope() {
		return scope;
	}

	public void setScope(ArrayList<String> scope) {
		Property.scope = scope;
	}

	public static String getDescription() {
		return description;
	}

	public void setDescription(String string) {
		Property.description = string;
	}

	public void setFormat(ArrayList<Object> format) {
		Property.format = format;
	}

	public static ArrayList<Object> getFormat() {
		return format;
	}

}
