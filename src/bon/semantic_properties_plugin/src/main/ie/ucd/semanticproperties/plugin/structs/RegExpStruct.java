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
import ie.ucd.semanticproperties.plugin.api.SemanticPropertyInstance;
import ie.ucd.semanticproperties.plugin.customobjects.Keyword;
import ie.ucd.semanticproperties.plugin.customobjects.MyDescription;
import ie.ucd.semanticproperties.plugin.customobjects.MyExpression;
import ie.ucd.semanticproperties.plugin.customobjects.MyFloat;
import ie.ucd.semanticproperties.plugin.customobjects.MyInt;
import ie.ucd.semanticproperties.plugin.customobjects.MyObject;
import ie.ucd.semanticproperties.plugin.customobjects.MyString;
import ie.ucd.semanticproperties.plugin.customobjects.Nat;
import ie.ucd.semanticproperties.plugin.exceptions.InvalidSemanticPropertyUseException;

import org.antlr.stringtemplate.*;
import org.antlr.stringtemplate.language.*;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

/**
 * Class that represents a Regular Expression.
 * <p>
 * Adds information to a regular expression about what is stored in its
 * capturing groups and provides methods to access these values.
 * </p>
 * 
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
  private HashMap<String, ArrayList<Integer>> positionMap;
  /**
   * Map representing the Objects in the capturing group of this RegExp.
   */
  private HashMap<String, Object> objectMap;
  /**
   * Type of RegExpStruct this is.
   */
  private RegType typeOfReg;
  /**
   * Number of positions in this RegExpStruct.
   */
  private int totalPositions;

  /**
   * Default constructor. Initialise all variables to default value.
   */
  public RegExpStruct() {
    exp = "";
    positionMap = new LinkedHashMap<String, ArrayList<Integer>>();
    objectMap = new LinkedHashMap<String, Object>();
    typeOfReg = RegType.NORMAL;
    totalPositions = 0;
  }

  /**
   * Constructor for objects.
   * 
   * @param s
   *          String representation of the regular expression.
   * @param m
   *          LinkedHashMap representing capturing groups.
   * @param num
   *          Number of capturing groups.
   */
  public RegExpStruct(Object o) {
    exp = "";
    positionMap = new LinkedHashMap<String, ArrayList<Integer>>();
    objectMap = new LinkedHashMap<String, Object>();
    typeOfReg = RegType.NORMAL;

    if (o instanceof MyObject) {
      MyObject temp = (MyObject) o;
      objectMap.put(temp.getId(), temp);
      ArrayList<Integer> oneList = new ArrayList<Integer>();
      oneList.add(1);
      positionMap.put(temp.getId(), oneList);
      exp += temp.getKind().getReg();
      totalPositions = 1;

    } else if (o instanceof String) {

      exp += (String) o;
      totalPositions = 0;
    } else if (o instanceof Keyword) {

      Keyword temp = (Keyword) o;
      objectMap.put(temp.getKeyword(), temp);
      ArrayList<Integer> l = new ArrayList<Integer>();
      l.add(1);
      positionMap.put(temp.getKeyword(), l);
      exp += "(" + temp.getValue() + ")";
      totalPositions = 1;
    }
  }

  /**
   * Constructor for choice, option.. etc.
   * 
   * @param p
   */
  public RegExpStruct(RegType p) {
    exp = "";
    positionMap = new LinkedHashMap<String, ArrayList<Integer>>();
    objectMap = new LinkedHashMap<String, Object>();
    typeOfReg = p;
    totalPositions = 0;
    if (p.equals(RegType.OPTIONAL)) {
      exp = "(?:)?";
    } else if (p.equals(RegType.CHOICE)) {
      exp = "(?:)";
    }
  }

  /**
   * Add RegExoStruct on to this one.
   */
  public void add(RegExpStruct toAdd) {
    String space = "[\\s]+";
    String optionalSpace = "[\\s]*";
    /**
     * Adjust exp.
     */
    if (typeOfReg.equals(RegType.NORMAL)) {
      /**
       * if exp is empty dont add space
       */
      if ((exp.equals(""))) {
        exp = toAdd.exp;
      } else {
        /**
         * case where list item is optional space before must also be optional
         */
        if (toAdd.typeOfReg.equals(RegType.OPTIONAL)) {
          exp = exp + optionalSpace + toAdd.exp;
        } else {
          exp = exp + space + toAdd.exp;
        }
      }
    } else if (typeOfReg.equals(RegType.OPTIONAL)) {
      String temp = exp.substring(3, exp.length() - 2);
      /**
       * No space before if it is first REgExpStuct for this option.
       */
      if ((temp.equals(""))) {
        temp = toAdd.exp;
      } else {
        temp = temp + space + toAdd.exp;

      }
      exp = "(?:" + temp + ")?";

    } else if (typeOfReg.equals(RegType.CHOICE)) {
      String temp = exp.substring(3, exp.length() - 1);
      /**
       * add on choice. No | before if it is first choice.
       */
      if ((temp.equals(""))) {
        temp = toAdd.exp;
      } else {
        temp = temp + "|" + toAdd.exp;
      }

      exp = "(?:" + temp + ")";

    }

    /**
     * Adjust all maps items in toAdd and add them to this.
     */
    for (String key : toAdd.positionMap.keySet()) {
      /**
       * Adjust positionMap.
       */
      ArrayList<Integer> newArray = toAdd.positionMap.get(key);
      // Adjust int[].
      for (int i = 0; i < newArray.size(); i++) {
        newArray.set(i, newArray.get(i) + totalPositions);
      }
      // Add new positions if it does not already exist
      if (this.positionMap.get(key) == null) {
        this.positionMap.put(key, newArray);
      }
      // if it does exist add diff values.
      else if (this.positionMap.get(key) != null) {
        ArrayList<Integer> oldArray = this.positionMap.get(key);
        // add oldArray and new Array.
        for (int i = 0; i < newArray.size(); i++) {
          oldArray.add(newArray.get(i));

        }
        this.positionMap.put(key, oldArray);
      }
      /**
       * Adjust objectMap.
       */
      this.objectMap.put(key, toAdd.objectMap.get(key));
    }

    /**
     * Adjust total positions.
     */
    totalPositions += toAdd.totalPositions;
  }

  public HashMap<String, Object> match(String input)
      throws InvalidSemanticPropertyUseException {
    HashMap<String, Object> captured = new HashMap<String, Object>();
    /**
     * Match Instance
     */
    Pattern p = Pattern.compile(exp);
    Matcher m = p.matcher(input);
    if (!m.matches()) {
      throw new InvalidSemanticPropertyUseException();
    }
    /**
     * Fill HashMap with the captured variables for this Instance.
     */
    HashMap<String, ArrayList<Integer>> intMap = positionMap;
    HashMap<String, Object> obMap = objectMap;
    // LinkedList<String> stringMap = new LinkedList <String>();
    // int start = 0;
    for (String s : obMap.keySet()) {

      Object obe = obMap.get(s);
      if (obe instanceof MyObject) {
        MyObject ob = (MyObject) obe;
        ArrayList<Integer> g = intMap.get(s);

        for (int k = 0; k < g.size(); k++) {

          int i = g.get(k);
          // fill only with non null values
          if ((m.group(i) != null)) {
            if (ob instanceof MyString) {
              String toSet = m.group(i);
              ob.setValue(toSet.substring(1, toSet.length() - 1));
            } else if (ob instanceof MyExpression) {
              String toSet = m.group(i);
              ob.setValue(toSet.substring(1, toSet.length() - 1));
            } else if (ob instanceof MyDescription) {
              String toSet = m.group(i);
              ob.setValue(toSet.substring(0, toSet.length() - 1));
            } else if (ob instanceof Nat) {
              Integer toSet = Integer.parseInt(m.group(i));
              ob.setValue(toSet);
            } else if (ob instanceof MyInt) {
              Integer toSet = Integer.parseInt(m.group(i));
              ob.setValue(toSet);
            } else if (ob instanceof MyFloat) {
              float toSet = Float.valueOf(m.group(i)).floatValue();
              ob.setValue(toSet);
            } else {
              ob.setValue(m.group(i));
            }
            captured.put(s, ob.getValue());
          }
        }
      } else if (obe instanceof Keyword) {
        ArrayList<Integer> g = intMap.get(s);
        String cap = "";
        // get valid int for the match
        for (int pres : g) {
          // fix later

          if (m.group(pres) != null) {
            cap = m.group(pres);
          }

        }

        captured.put(s, cap);
      }

    }
    return captured;
  }



  /**
   * Used for testing equivalence of two RegExpStructs.
   */
  public static boolean equals(final RegExpStruct r1, final RegExpStruct r2) {
    if (!r1.exp.equals(r2.exp)) {
      return false;
    }
    if (!(r1.totalPositions == r2.totalPositions)) {
      return false;
    }
    if (!(r1.typeOfReg.equals(r2.typeOfReg))) {
      return false;
    }
    /**
     * Compare objectMaps and intMaps..
     */
    if (r1.objectMap.size() != r2.objectMap.size()) {
      return false;
    }
    if (r1.positionMap.size() != r2.positionMap.size()) {
      return false;
    }
    Iterator obIt = r1.objectMap.keySet().iterator();
    while (obIt.hasNext()) {
      String key = (String) obIt.next();
      /**
       * ob map
       */
      if (r2.objectMap.get(key) instanceof MyObject) {
        MyObject t1 = (MyObject) r2.objectMap.get(key);
        MyObject t2 = (MyObject) r1.objectMap.get(key);

        if (!(t1.equals(t2))) {
          return false;
        }
        if (!(t1.equals(t2))) {
          return false;
        }
      }
      /**
       * int map
       */
      if (!r2.positionMap.get(key).equals(r1.positionMap.get(key))) {
        return false;
      }
    }
    return true;
  }

  /**
   * Getter used for testing.
   * 
   * @return
   */

  public LinkedHashMap<String, Object> getGroupObj() {

    return (LinkedHashMap) objectMap;
  }

  /**
   * Getter used for testing.
   * 
   * @return the exp
   */
  public String getExp() {
    return exp;
  }

  /**
   * Getter used for testing.
   * 
   * @return the totalPositions
   */
  public int getTotalPositions() {
    return totalPositions;
  }

}
