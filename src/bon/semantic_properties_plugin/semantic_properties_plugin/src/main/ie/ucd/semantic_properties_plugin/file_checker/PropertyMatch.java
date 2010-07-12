
package ie.ucd.semantic_properties_plugin.file_checker;

import java.util.regex.Matcher;
import java.util.regex.Pattern;
/**Class that represents a match between a Property and an input.
 * 
 * @author eo
 *
 */
public class PropertyMatch {
	
	private String inputToMatch;
	private Matcher thisMatch;
	Property prop;
	Boolean isMatch;
	
	/**
	 * 
	 * @param input 
	 * @param prop
	 */
	PropertyMatch(String input,Property propIn){
		prop = propIn;
		inputToMatch = input;
		Pattern p = Pattern.compile(propIn.getReg().getExp());
		thisMatch = p.matcher(input);
		isMatch = thisMatch.matches();
		
	}
	/**Determines if this match is valid.
	 * @param true if this is a valid match
	 */
	public boolean isValid(){
		return isMatch;
	}
	public String getVar(String in){
		int i=prop.getReg().getGroups().get(in);
		return thisMatch.group(i);
		
	}
	public Property getProp() {
		return prop;
	}
	public Matcher getThisMatch() {
		return thisMatch;
	}
	public String getInputToMatch() {
		return inputToMatch;
	}

	
}
