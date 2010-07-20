/**
 * @title "Semantic LevelRepresenation Plugin Package"
 * @description "Class that represents a Regular Expression"
 * @author  Eoin O'Connor
 * @copyright ""
 * @license "Public Domain."
 * @version "$Id: 01-07-2010 $"
 */
package ie.ucd.semantic_properties_plugin.file_checker;


/**
 * <p> A string representation of a Regular Expression 
 * and a map of what to store in the capturing  groups  .</p>
 *
 * @see   LevelRepresenation
 * @version "$Id: 01-07-2010 $"
 * @author  eo
 **/
import java.util.LinkedHashMap;

import semantic_properties_plugin.custom_objects.MyObject;

/**Class that represents a Regular Expression.
 * <p>Adds information to a regular expression about what is 
 * stored in its capturing groups and provides methods to 
 * access these values.</p>
 * @author eo
 *
 */
public class RegExpStruct {
	/**String representation of the  RegExp.
	 * 
	 */
	private String exp;
	/**Map representing the values in the capturing group of this RegExp.
	 * 
	 */
	private LinkedHashMap <String, Integer> groupInt;
	/**Map representing the Objects in the capturing group of this RegExp.
	 * 
	 */
	private LinkedHashMap <String, MyObject> groupObj;
	/**Number of capturing groups in this regExp.
	 * 
	 */
	private int numberOfGroups;

	/**Default constructor.
	 * <p> initialise all variables to unimportant value.</p>
	 */
	RegExpStruct() {
		exp = "";
		groupInt = new LinkedHashMap<String, Integer>();
		groupObj = new LinkedHashMap<String, MyObject>();
		numberOfGroups = 0;
	}
	/**Constructor .
	 * 
	 * @param s String representation of the regular expression.
	 * @param m LinkedHashMap  representing capturing groups.
	 * @param num Number of capturing groups.
	 */
	RegExpStruct(String s, LinkedHashMap<String, Integer> m, LinkedHashMap<String, MyObject> objectMap, int num) {
		exp = s;
		groupInt = m;
		numberOfGroups = num;
		groupObj=objectMap;
	}
	/**Method that adds a RegExpStruct on to this one.
	 * <p>Adds both String rep and map</p>
	 * @return concatenated RegExpStruct.
	 * @param toAdd RegExpStruct to add on end.
	 * @param pre String to add to start of  whole regEx
	 * @param post String to add to end of regEx
	 * @param additionalGroups group produced by adding pre and post.
	 */
	public RegExpStruct concat(RegExpStruct toAdd,String pre,String post,int additionalGroups){
		
		String newExp = pre + exp + toAdd.getExp() + post;
		int newNum = numberOfGroups 
		+ toAdd.getNumberOfGroups() + additionalGroups;
		
		/**Concat the linkedHashMaps
		 * 
		 */
		LinkedHashMap<String, Integer> newIntGroup=groupInt;
		LinkedHashMap<String, Integer> addGroup=toAdd.getGroupInt();
		for(String key :addGroup.keySet()){
			newIntGroup.put(key, addGroup.get(key)+numberOfGroups);
		}
		
		LinkedHashMap<String, MyObject> newObjGroup= new LinkedHashMap<String, MyObject>();
		newObjGroup.putAll(toAdd.getGroupObj());

		return (new RegExpStruct(newExp,newIntGroup,newObjGroup,newNum));
		
	}
	
	
	

	
	public String getExp() {
		return exp;
	}


	public int getNumberOfGroups() {
		return numberOfGroups;
	}

	public void setNumberOfGroups(int numberOfGroups) {
		this.numberOfGroups = numberOfGroups;
	}

	public LinkedHashMap<String, Integer> getGroupInt() {
		return groupInt;
	}

	public void setGroups(LinkedHashMap<String, Integer> groups) {
		this.groupInt = groups;
	}

	public void setExp(String exp) {
		this.exp = exp;
	}
	public LinkedHashMap<String, MyObject> getGroupObj() {
		return groupObj;
	}

}
