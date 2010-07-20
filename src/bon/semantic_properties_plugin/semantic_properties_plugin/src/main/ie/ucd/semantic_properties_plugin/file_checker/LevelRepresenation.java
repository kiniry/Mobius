/**
 * @title "Semantic LevelRepresenation Plugin Package"
 * @description "Class that represents,checks and generates a regexp for a semantic property."
 * @author  Eoin O'Connor
 * @copyright ""
 * @license "Public Domain."
 * @version "$Id: 01-07-2010 $"
 */

package ie.ucd.semantic_properties_plugin.file_checker;

import java.io.File;
import java.io.FileInputStream;
import java.util.ArrayList;
import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.Map;
import java.util.Set;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import org.yaml.snakeyaml.Dumper;
import org.yaml.snakeyaml.DumperOptions;
import org.yaml.snakeyaml.Loader;
import org.yaml.snakeyaml.Yaml;

import custom_yaml.CustomConstructor;
import custom_yaml.CustomRepresenter;
import custom_yaml.CustomResolver;


import semantic_properties_plugin.custom_objects.MyObject;


/**A class representing a semantic property.
 * <p> A class representing a semantic property that consists of
 * format,name,scope,description and a regular expression structure.</p>
 *
 * @see    RegExpStruct
 * @version "$Id: 01-07-2010 $"
 * @author  Eoin O'Connor
 **/

public class LevelRepresenation {

	/**Strings Used for Validity Checks.
	 * <p> Definition of what makes an acceptable property fors
     *  name,scope,description and the different format possibilities </p>
	 */
	final static String prop_Scope = "(files|modules|features|variables|all|special)";
	final static String prop_Description = ".*";
	final static String prop_format_String = "(\\w*)";
	final static String prop_format_CustomObject = "(\\w+=(\\w|[0-9]|\\.)+)";
	final static String prop_format_Special = "((choice\\s*\\((\\w+)\\)\\s*)|choice|optional)";	
	final static String prop_Name = "\\s*\\w+\\s*";
	final static String prop_Level = "[=-]?\\d+";


	/**The variables for a property
	 * <p>  list of property attributes </p>
	 */
	private static ArrayList<Object> format;
	private static ArrayList<String> scope;
	private static String description;
	private static String name;
	private int level;
	private RegExpStruct reg;
	
	/**Constructor for  linkedHashMap.
	 * @param input linkedHashMap with property in it.
	 */
	public LevelRepresenation(LinkedHashMap< String , ? > input) {
		parse(input);
	}
	
	
	/**Constructor for  yaml File.
	 * @param input yaml file with property in it.
	 */
	public LevelRepresenation(File input) {
		Yaml yaml = new Yaml(new Loader(new CustomConstructor()), new Dumper(
				new CustomRepresenter(), new DumperOptions()),
				new CustomResolver());;
		FileInputStream io=null;

		try {
			io = new FileInputStream(input);
		} catch (Exception e) {
			System.out.println("invalid string");
		}
		Object ob = yaml.load(io);
		parse((LinkedHashMap<String, ?>) ob);

	}

	/**Constructor for string with yaml content.
	 * @param input String representing input file
	 */
	public LevelRepresenation (String input) {
			Yaml yaml = new Yaml(new Loader(new CustomConstructor()), new Dumper(
					new CustomRepresenter(), new DumperOptions()),
					new CustomResolver());;

			Object ob =yaml.load(input);
			parse((LinkedHashMap<String,?>)ob);

	}
	
	/**parse method for LinkedHashMap.
	  * <p>method takes in snakyaml parsed linkedHashMap
	  * and fills this property's values</p>
	  * @param linkedHashMap to parse
	  */

	private void parse(LinkedHashMap<String , ?> linkedHashMap) {
		
			if(!checkValidity(linkedHashMap)){
				System.out.println("linkedHashMap entery "+linkedHashMap+" does not represent a valid property not valid");
			}
			else{
				name=(String)linkedHashMap.get("name");
				format=(ArrayList<Object>)linkedHashMap.get("format");
				description=(String)linkedHashMap.get("description");
				scope=(ArrayList<String>)linkedHashMap.get("scope");		  
				reg= generateRegExp();
				level=Integer.parseInt((String)linkedHashMap.get("level"));
			}
					
			  
	}
	/**Checks validity of property.
	 * <p>Checks prop for validity as defined by the strings at 
	 * the beginning of this file</p>
	 * @param newProp linkedHashMap that contains potential property as parsed by snakeyaml
	 * @return true when the property is  valid.
	 */
	private boolean checkValidity(LinkedHashMap<String, ?> newProp) {



		/**Checks the level ;
		 * 
		 */
		Pattern levelPattern = Pattern.compile(prop_Level);

		Matcher levelMatcher = levelPattern.matcher((String)newProp.get("level"));
		if (!levelMatcher.matches()) {
			System.out.println(" level value is invalid @" + name);
			return false;
		}
		/**Checks the name ;
		 * 
		 */
		Pattern namePattern = Pattern.compile(prop_Name);

		Matcher nameMatcher = namePattern.matcher((String)newProp.get("name"));
		if (!nameMatcher.matches()) {
			System.out.println(" name value is invalid @" + name);
			return false;
		}

		/**Checks the scope;
		 * 
		 */
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

		/**Checks the description
		 * 
		 */
		Pattern descriptionPattern = Pattern.compile(prop_Description,
				Pattern.DOTALL);
		Matcher descriptionMatcher = descriptionPattern.matcher((String)newProp.get("description"));
		if (!descriptionMatcher.matches()) {
			System.out.println("The  properties description is invalid @"
					+ description);
			return false;
		}

		/*Checks the format with recursive method
		 * 
		 */
		return checkFormatValidity((ArrayList<Object>)newProp.get("format"));

	}
	/**
	 * recursive method to check if object is a valid format property.
	 * @param formatValue Object to be checked
	 * @return true when object is a valid format object
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

	private static RegExpStruct generateRegExp() {
		RegExpStruct returnRegEx = generateRegExp(format);
		String start=name+"[\\s+]";
		String end=returnRegEx.getExp();
		returnRegEx.setExp(start+end);
		return returnRegEx;
	}
	/**
	 * Recursive method to build RegeExpStruct for an object
	 * @param ob object to generate RegExpStruct from
	 * @return RegExpStruct representation of object 
	 */

	private static RegExpStruct generateRegExp(Object ob) {
		String space="[\\s+]";

		/*ArrayList Case
		 * 
		 */
		if (ob instanceof ArrayList< ? >) {
		
			ArrayList< ? > list = (ArrayList< ? >) ob;	
			/*loop through RegExpStruct and add eachRegExpStruct to end.
			 * <p>loop through all objects in list, generate RegExpStruct
			 * and add them to rlist</p>
			 */
			RegExpStruct listReg = new RegExpStruct();
			for (Object obin : list) {
				RegExpStruct temp = generateRegExp(obin);
				String end = space;
				//if obon is optional case we add space beginning inside brackets.
				if (temp.getExp().endsWith(")?")) {
					String l = temp.getExp(); 
					temp.setExp("(?:"+space+l.substring(3,l.length()));
					listReg = listReg.concat(temp,"", "", 0);
				} else {
					temp = temp.concat(new RegExpStruct(), space, "", 0);
					listReg = listReg.concat(temp, "", "", 0);
				}
			}
			/**Get rid of extra space on beginning.
			 * 
			 */
			if (listReg.getExp().startsWith(space)) {
				String l = listReg.getExp();
				listReg.setExp(l.substring(space.length(), l.length() ));
			}
			return listReg;
			

		}
		/**Map Case
		 * 
		 */
		if (ob instanceof LinkedHashMap<?, ?>) {		
			/**Cast to LinkeHashMap and make new RegExpStuct.;
			 * 
			 */
			RegExpStruct choiceCapReg = new RegExpStruct();
			LinkedHashMap<String, ?> all = (LinkedHashMap<String, ?>) ob;
			/** choice:(name) sub-case
			 * <p>This is the capturing case</p>
			 */
			
			/*Check if its a capturing choice case
			 * <p>break is not</>
			 */
			
			Set<String> keys=all.keySet();
			for(String s :keys){
				String check="choice\\s*\\((\\w+)\\)\\s*";
				Pattern checkPattern = Pattern.compile(check);
				Matcher checkMatcher = checkPattern.matcher(s);
				if (!checkMatcher.matches()) {
				   //if not special case exit
					break;
				}
				/**Get regExpStruct,Map add choice and set as regExpStruct map again.
				 * <p>Because its the capturing case</p>
				 */
				LinkedHashMap<String ,Integer> capRegGroup =
				choiceCapReg.getGroupInt();
				
				capRegGroup.put(checkMatcher.group(1),capRegGroup.size()+1);
				
				choiceCapReg.setGroups(capRegGroup);
				choiceCapReg.setNumberOfGroups(choiceCapReg.getNumberOfGroups()+1);
				/**Get list of choices
				 * 
				 */
				ArrayList<?> choices=(ArrayList<?>)all.get(s);	
				/**Loop through list choices and build RegExpStruct.
				 * 
				 */
				for (Object obin : choices) {
					RegExpStruct temp = generateRegExp(obin);
					choiceCapReg = choiceCapReg.concat(temp, "", "|",0);
				}
				/**Get rid of extra '|'.
				 * 
				 */
				String l=choiceCapReg.getExp();
				choiceCapReg.setExp(l.substring(0,l.length()-1));
				choiceCapReg=choiceCapReg.concat(new RegExpStruct(), "(", ")", 0);
				return choiceCapReg;
				
			}
			/** choice: sub-case
			 * <p>This is the non capturing case</p>
			 */
			
			if (all.containsKey("choice")) {
				/**Get list of choices
				 * 
				 */
				ArrayList< ? > choices = (ArrayList< ? >) all.get("choice");	
				/**Loop through list choices and build RegExpStruct.
				 * 
				 */
				for (Object obin : choices) {
					RegExpStruct temp = generateRegExp(obin);
					choiceCapReg = choiceCapReg.concat(temp, "", "|", 0);
				}
				/**Get rid of extra '|'.
				 * 
				 */
				String l=choiceCapReg.getExp();
				choiceCapReg.setExp(l.substring(0,l.length()-1));
				choiceCapReg = choiceCapReg.concat(new RegExpStruct(), "(?:", ")", 0);
				return choiceCapReg;

				
				
				
			}
			// optional case
			if (all.containsKey("optional")) {
				RegExpStruct opt = new RegExpStruct();
				Object optionOb = all.get("optional");
				RegExpStruct optionReg = generateRegExp(optionOb);
				
				String ex = "(?:" + optionReg.getExp() + ")?";					
				LinkedHashMap<String, Integer> optionMap = new LinkedHashMap<String, Integer>();
	//			optionMap.put(optionReg.getExp(), 1);
				opt=opt.concat(optionReg, "(?:", ")?", 0);
				return opt;
							
			}			
			return choiceCapReg;

		}
		//   if string
		if (ob instanceof String) {

			return new RegExpStruct(
					(String) ob,
					new LinkedHashMap<String, Integer>(),
					new LinkedHashMap<String, MyObject>(),
					0);

		}
		// custom objects
		if (ob instanceof MyObject) {
			//cast to MyObject.
			MyObject thisOb = (MyObject) ob;
			
			LinkedHashMap<String, Integer> intMap = 
				new LinkedHashMap<String, Integer>();
			intMap.put(thisOb.getId(), 1);

			LinkedHashMap<String, MyObject> objMap = 
				new LinkedHashMap<String, MyObject>();
			objMap.put(thisOb.getId(), thisOb);
			
			return new RegExpStruct(thisOb.getReg(), 
					intMap, objMap, 1);

		} else{
			return new RegExpStruct(
					"unexpected type encountered when generating RegExp" 
					+ " in Propery.class"
					+ ob, new LinkedHashMap<String, Integer>(),
					new LinkedHashMap<String, MyObject>(), 0);

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
	/**Could be deleted in future.
	 * method to check an input string against this proerty
	 * @return Matcher of input string against the regexof this property
	 * @param in string to match against the regex representation of this string
	 */
	public boolean isProperty(String in){
		Pattern p= Pattern.compile(reg.getExp());
		Matcher m=p.matcher(in);
		return m.matches();
		
	}
	public static String getName() {
		return name;
	}

	public static void setName(String name) {
		LevelRepresenation.name = name;
	}

	public static ArrayList<String> getScope() {
		return scope;
	}

	public void setScope(ArrayList<String> scope) {
		LevelRepresenation.scope = scope;
	}

	public static String getDescription() {
		return description;
	}

	public void setDescription(String string) {
		LevelRepresenation.description = string;
	}

	public static ArrayList<Object> getFormat() {
		return format;
	}
	public void setFormat(ArrayList<Object> format) {
		LevelRepresenation.format = format;
	}

	public int getLevel() {
		return level;
	}

}
