package ie.ucd.semantic_properties_plugin.file_checker;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.regex.*;

public class Property {
	
	//definition of exceptable properties using regular expressions
	
	final static String prop_Scope = "(files|modules|features|variables|all|special)";
	final static String prop_Description = ".*";
	final static String prop_Name="(.*|[(.*,)*.*]|optional:.*)";
	
	// class variables
	private static ArrayList<String> name;
	private static ArrayList<String> scope;
	private static String description;
	
	public Property(){
		name=new ArrayList<String>();
		scope= new ArrayList<String>();
		description= new String();
		
	}
	
	public static ArrayList<String> getName() {
		return name;
	}
	public void setName(ArrayList<String> name) {
		Property.name = name;
	}
	public static ArrayList<String> getScope() {
		return scope;
	}
	public  void setScope(ArrayList<String> scope) {
		Property.scope = scope;
	}
	public static String getDescription() {
		return description;
	}
	public  void setDescription(String string) {
		Property.description = string;
	}
	public boolean checkValidity(){
		Pattern scopePattern = Pattern.compile(prop_Scope, Pattern.CASE_INSENSITIVE);
		Pattern descriptionPattern = Pattern.compile(prop_Description, Pattern.DOTALL);
		Pattern namePattern = Pattern.compile(prop_Name);
		
		//check scopes
		for( String scopeValue : scope){
			Matcher scopeMatcher = scopePattern.matcher(scopeValue);
			if(!scopeMatcher.matches()){
				System.out.println(name+" scope value is invalid @"+scopeValue);
				return false;
			}
		}
		
		// check Description
		Matcher descriptionMatcher = descriptionPattern.matcher(description);
		if(!descriptionMatcher.matches()){
			System.out.println("The  properties description is invalid @"+ description);
			return false;
		}
		
		//check name
		for( Object nameValue : name){
			
			//case for normal property
			if(nameValue instanceof String){
				Matcher nameMatcher = namePattern.matcher((String)nameValue);
				if(!nameMatcher.matches()){
					System.out.println(" name value is invalid @"+nameValue);
					return false;
				}
			}
			//case for optinal inner list [a,b,c]
			else if(nameValue instanceof ArrayList<?>){
				for(String optionalNameValue :(ArrayList<String>)nameValue){
					Matcher nameMatcher = namePattern.matcher(optionalNameValue);
					if(!nameMatcher.matches()){
						System.out.println(" an optional name value is invalid @"+nameValue);
						return false;
					}
					
				}
				
			}
			// any case i didnt predict
			else{
				System.out.println("Should not have got here in name check, reason @ "+ nameValue);
			}
			
		}
				
			
		return true;
	}

}
