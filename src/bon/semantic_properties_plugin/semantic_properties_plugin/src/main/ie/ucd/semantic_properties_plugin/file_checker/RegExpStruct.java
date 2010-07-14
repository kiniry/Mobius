/**
 * @title "Semantic Property Plugin Package"
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
 * @see   Property
 * @version "$Id: 01-07-2010 $"
 * @author  eo
 **/
import java.util.LinkedHashMap;

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
	private LinkedHashMap <String, Integer> groups;
	/**Map representing the Objects in the capturing group of this RegExp.
	 * 
	 */
	private LinkedHashMap <Object, Integer> customGroup;
	/**Number of capturing groups in this regExp.
	 * 
	 */
	private int numberOfGroups;

	/**Default constructor.
	 * <p> initialise all variables to unimportant value.</p>
	 */
	RegExpStruct() {
		exp = "";
		groups = new LinkedHashMap<String, Integer>();
		numberOfGroups = 0;
	}
	/**Constructor .
	 * 
	 * @param s String representation of the regular expression.
	 * @param m LinkedHashMap  representing capturing groups.
	 * @param num Number of capturing groups.
	 */
	RegExpStruct(String s, LinkedHashMap<String, Integer> m, int num) {
		exp = s;
		groups = m;
		numberOfGroups = num;
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
		
		String newExp=pre+exp+toAdd.getExp()+post;
		int newNum=numberOfGroups+toAdd.getNumberOfGroups()+additionalGroups;
		
		/**Concat the linkedHashMaps
		 * 
		 */
		LinkedHashMap<String, Integer> newGroup=groups;
		LinkedHashMap<String, Integer> addGroup=toAdd.getGroups();
		for(String key :addGroup.keySet()){
			newGroup.put(key, addGroup.get(key)+numberOfGroups);
		}
		
		return (new RegExpStruct(newExp,newGroup,newNum));
		
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

	public LinkedHashMap<String, Integer> getGroups() {
		return groups;
	}

	public void setGroups(LinkedHashMap<String, Integer> groups) {
		this.groups = groups;
	}

	public void setExp(String exp) {
		this.exp = exp;
	}

}
