
package ie.ucd.semanticproperties.plugin.structs;

import ie.ucd.semanticproperties.plugin.customobjects.MyObject;

import java.util.regex.Matcher;
import java.util.regex.Pattern;

/**Class that represents a match between a LevelRepresenation and an input.
 * 
 * @author eo
 *
 */
public class LevelRepMatch {

  private String inputToMatch;
  private Matcher thisMatch;
  LevelRepresenation prop;
  Boolean isMatch;

  /**
   * 
   * @param input 
   * @param prop
   */
  public LevelRepMatch(String input,LevelRepresenation propIn){
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
  /**Get the MyObject named by in.
   * 
   * @param in name of theMyObject to retrieve.
   * @return the MyObject
   */
  public MyObject getVar(String in) {
    /**
     *<p>/check if a variable with this name exists.
     *if true return MyObject with te alue from this match. 
     *if false return null if it dosn't</p> 
     */

    if (prop.getReg().getGroupInt().get(in) != null) {
      int i = prop.getReg().getGroupInt().get(in);
      MyObject ob= prop.getReg().getGroupObj().get(in);
      ob.setValue(thisMatch.group(i));
      return ob;
    } else {
      return null;
    }

  }
  public LevelRepresenation getProp() {
    return prop;
  }
  public Matcher getMatch() {
    return thisMatch;
  }
  public String getInputToMatch() {
    return inputToMatch;
  }


}
