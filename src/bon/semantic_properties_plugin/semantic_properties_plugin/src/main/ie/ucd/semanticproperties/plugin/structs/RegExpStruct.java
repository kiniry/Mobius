/**
 * @title "Semantic LevelRepresenation Plugin Package"
 * @description "Class that represents a Regular Expression"
 * @author  Eoin O'Connor
 * @copyright ""
 * @license "Public Domain."
 * @version "$Id: 01-07-2010 $"
 */
package ie.ucd.semanticproperties.plugin.structs;

/**
 * <p>
 * A string representation of a Regular Expression and a map of what to store in
 * the capturing groups .
 * </p>
 * 
 * @see LevelRepresenation
 * @version "$Id: 01-07-2010 $"
 * @author eo
 */
import ie.ucd.semanticproperties.plugin.customobjects.MyObject;

import org.antlr.stringtemplate.*;
import org.antlr.stringtemplate.language.*;
import java.util.Arrays;
import java.util.Iterator;
import java.util.LinkedHashMap;

/**
 * Class that represents a Regular Expression.
 * <p>
 * Adds information to a regular expression about what is stored in its
 * capturing groups and provides methods to access these values.
 * </p>
 * @author eo
 */
public class RegExpStruct {
  /**
   * String representation of the RegExp.
   */
  private String exp;
  /**
   * Map representing the values in the capturing group of this RegExp.
   */
  private LinkedHashMap<String, int[]> groupInt;
  /**
   * Map representing the Objects in the capturing group of this RegExp.
   */
  private LinkedHashMap<String, MyObject> groupObj;
  /**
   * Number of capturing groups in this regExp.
   */
  private int numberOfGroups;

  /**
   * Default constructor.
   * Initialise all variables to default value.
   */
  RegExpStruct() {
    exp = "";
    groupInt = new LinkedHashMap<String, int[]>();
    groupObj = new LinkedHashMap<String, MyObject>();
    numberOfGroups = 0;
  }

  /**
   * Constructor for objects.
   * @param s
   *          String representation of the regular expression.
   * @param m
   *          LinkedHashMap representing capturing groups.
   * @param num
   *          Number of capturing groups.
   */
  RegExpStruct(String s, LinkedHashMap<String, int[]> m,
      LinkedHashMap<String, MyObject> objectMap, int num) {
    exp = s;
    groupInt = m;
    numberOfGroups = num;
    groupObj = objectMap;
  }

  /**
   * Method that adds a RegExpStruct on to this one.
   * <p>
   * Adds both String rep and map
   * </p>
   * @return concatenated RegExpStruct.
   * @param toAdd
   *          RegExpStruct to add on end.
   * @param pre
   *          String to add to start of whole regEx
   * @param post
   *          String to add to end of regEx
   * @param additionalGroups
   *          group produced by adding pre and post.
   */
  public RegExpStruct concat(RegExpStruct toAdd, String pre, String post,int additionalGroups) {
    String newExp = pre + exp + toAdd.getExp() + post;
    int newNum = numberOfGroups + toAdd.getNumberOfGroups() + additionalGroups;

    /**
     * Concat the int linkedHashMap
     */
    LinkedHashMap<String, int[]> newIntGroup = groupInt;
    LinkedHashMap<String, int[]> addGroup = toAdd.getGroupInt();
    for (String key : addGroup.keySet()) {
      
      int[] newAddGroup = addGroup.get(key);
      for(int i=0;i<newAddGroup.length;i++){
        newAddGroup[i] = newAddGroup[i] + numberOfGroups;
      }
      newIntGroup.put(key, newAddGroup);

    }
    /**
     * Concat the obj linkedHashMap
     */

    LinkedHashMap<String, MyObject> newObjGroup = groupObj;
    newObjGroup.putAll(toAdd.getGroupObj());

    return (new RegExpStruct(newExp, newIntGroup, newObjGroup, newNum));

  }
  /**
   * 
   * Mehods to be used by new generate method--- delete this when implemetntation is completed.
   * @return
   */
  
  /**
   * Constructor that takes creates non capturing RegExpStuct for non capturing input string.
   */
  RegExpStruct(String input) {
    exp = input;
    groupInt = new LinkedHashMap<String, int[]>();
    groupObj = new LinkedHashMap<String, MyObject>();
    numberOfGroups = 0;
  }
  /**
   * Add RegExoStruct on to this one
   */
  RegExpStruct add(RegExpStruct toAdd){
    String newExp =  exp + toAdd.getExp();
    int newNum = numberOfGroups + toAdd.getNumberOfGroups();

    /**
     * Concat the int linkedHashMap
     */
    LinkedHashMap<String, int[]> newIntGroup = groupInt;
    LinkedHashMap<String, int[]> addGroup = toAdd.getGroupInt();
    for (String key : addGroup.keySet()) {
      int[] newAddGroup = addGroup.get(key);
      for(int i :newAddGroup){
        newAddGroup[i] = i + numberOfGroups;
      }
      newIntGroup.put(key, newAddGroup);
    }
    /**
     * Concat the obj linkedHashMap
     */

    LinkedHashMap<String, MyObject> newObjGroup = groupObj;
    newObjGroup.putAll(toAdd.getGroupObj());

    return (new RegExpStruct(newExp, newIntGroup, newObjGroup, newNum));
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

  public LinkedHashMap<String, int[]> getGroupInt() {
    return groupInt;
  }

  public void setGroups(LinkedHashMap<String, int[]> groups) {
    this.groupInt = groups;
  }

  public void setExp(String exp) {
    this.exp = exp;
  }

  public LinkedHashMap<String, MyObject> getGroupObj() {
    return groupObj;
  }
  public StringTemplate getPrettyPrint(){
    String i = "";
    for(String key:groupObj.keySet()){
      i += ("$"+ key+"$ ");
    }
    return new StringTemplate(i, DefaultTemplateLexer.class);
    
  }
  /**
   * Overwrite hashCode as we overwrote equals.
   */
  @Override
  public int hashCode() {
    final int prime = 31;
    int result = 1;
    result = prime * result + ((exp == null) ? 0 : exp.hashCode());
    result = prime * result + numberOfGroups;
    return result;
  }
  /**
   * Overwrite equals method as it dosn't like LinkedHahsMap.
   */

  @Override
  public boolean equals(Object obj) {
    if (this == obj)
      return true;
    if (obj == null)
      return false;
    if (getClass() != obj.getClass())
      return false;
    final RegExpStruct other = (RegExpStruct) obj;
    if (exp == null) {
      if (other.exp != null)
        return false;
    } else if (!exp.equals(other.exp))
      return false;
    if (groupInt == null) {
      if (other.groupInt != null)
        return false;
    } else if (!(compareLinkedHashMap(groupInt, other.getGroupInt())))
      return false;
    if (groupObj == null) {
      if (other.groupObj != null)
        return false;
    } else if (!(compareLinkedHashMap(groupObj,other.getGroupObj())))
      return false;
    if (numberOfGroups != other.numberOfGroups)
      return false;
    return true;
  }
  private Boolean compareLinkedHashMap(LinkedHashMap<String, ? > m1, LinkedHashMap<String, ? > m2) {

    if ( m1.size() != m2.size() ) {
      return false;
    }
    outerloop:for (String s : m1.keySet()) {
      if(!m2.containsKey(s)){
        return false;
      }
      Iterator i = m2.values().iterator();
      while(i.hasNext()){
        Object r = i.next();
        Object p = m1.get(s);
        if(r instanceof int[]){
          int [] nr = (int[]) r;
          int [] np = (int[]) p;
          if(Arrays.equals(np,nr)){
            break outerloop;
          }
        }
        else{
          if(r.equals(p)){
            break outerloop;
          }
        }
        
      }
      return false;
      
    }
    return true;
  }

}

