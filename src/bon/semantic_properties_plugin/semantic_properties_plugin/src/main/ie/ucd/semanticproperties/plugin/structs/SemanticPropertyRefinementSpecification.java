package ie.ucd.semanticproperties.plugin.structs;

import ie.ucd.semanticproperties.plugin.api.LevelId;
import ie.ucd.semanticproperties.plugin.api.ScopeId;
import ie.ucd.semanticproperties.plugin.api.SemanticPropertyInstance;
import ie.ucd.semanticproperties.plugin.customobjects.MyDescription;
import ie.ucd.semanticproperties.plugin.customobjects.MyExpression;
import ie.ucd.semanticproperties.plugin.customobjects.MyObject;
import ie.ucd.semanticproperties.plugin.customobjects.MyObjectKind;
import ie.ucd.semanticproperties.plugin.customobjects.MyString;
import ie.ucd.semanticproperties.plugin.customobjects.MyStringObject;
import ie.ucd.semanticproperties.plugin.exceptions.IncompatibleSemanticPropertyInstancesException;
import ie.ucd.semanticproperties.plugin.exceptions.InvalidRefinementException;
import ie.ucd.semanticproperties.plugin.exceptions.InvalidRefinementSpecificationException;
import ie.ucd.semanticproperties.plugin.exceptions.UnknownLevelException;
import ie.ucd.semanticproperties.plugin.exceptions.UnknownVariableIdentifierException;
import ie.ucd.semanticproperties.plugin.yaml.CustomConstructor;
import ie.ucd.semanticproperties.plugin.yaml.CustomRepresenter;
import ie.ucd.semanticproperties.plugin.yaml.CustomResolver;
import ie.ucd.semanticproperties.plugin.yaml.RefinementConstructor;
import ie.ucd.semanticproperties.plugin.yaml.RefinementRepresenter;
import ie.ucd.semanticproperties.plugin.yaml.RefinementResolver;

import java.io.File;
import java.io.FileInputStream;
import java.io.FileNotFoundException;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.Set;
import java.util.StringTokenizer;
import java.util.Map.Entry;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import org.yaml.snakeyaml.Dumper;
import org.yaml.snakeyaml.DumperOptions;
import org.yaml.snakeyaml.Loader;
import org.yaml.snakeyaml.Yaml;



/**Stores a refinement property from one level to another. 
 * 
 * @author eo
 *
 */
public class SemanticPropertyRefinementSpecification {

  private LinkedHashMap<String,String> sConversions;
  private LinkedHashMap<String, Transitions> oConversions;
  private LevelId sourceLevel;
  private LevelId destinationLevel;
  private String propertyName;


  /**Constructor for  Object.
   * @param input object with property in it.
   * @throws UnknownLevelException 
   */
  public SemanticPropertyRefinementSpecification(Object input) throws UnknownLevelException, InvalidRefinementSpecificationException {
    parse(input);

  }
  /**Constructs Refinement LevelRepresenation from input String. 
   *
   * @param input string in yaml form to parse.
   * @throws UnknownLevelException 
   * @throws FileNotFoundException 
   */
  public SemanticPropertyRefinementSpecification(final String input) throws UnknownLevelException , InvalidRefinementSpecificationException{

    Yaml yaml = new Yaml(new Loader(new RefinementConstructor()), new Dumper(new RefinementRepresenter(), new DumperOptions()), new RefinementResolver());
    Object ob = yaml.load(input);
    parse(ob);
  }
  /**Constructs Refinement LevelRepresenation from input file. 
   * 
   * @param input file to parse
   * @throws UnknownLevelException 
   * @throws FileNotFoundException 
   * @throws FileNotFoundException 
   */
  public SemanticPropertyRefinementSpecification(final File input) throws UnknownLevelException, FileNotFoundException, InvalidRefinementSpecificationException {

    Yaml yaml = new Yaml(new Loader(new RefinementConstructor()), new Dumper(new RefinementRepresenter(), new DumperOptions()), new RefinementResolver());
    FileInputStream io = new FileInputStream(input);
    Object ob = yaml.load(io);
    parse(ob);
  }
  /**parse object for values of Refinement LevelRepresenation.
   * 
   * @param currentOb Object to parse.
   * @throws UnknownLevelException 
   */
  private void parse(final Object currentOb) throws UnknownLevelException, InvalidRefinementSpecificationException {
    /**Entry case
     * <p>We assume key is string.Possibly fix this later. </p>
     */
    if (currentOb instanceof Entry< ? , ? >) {
      Entry<Object, Object> ent = (Entry<Object, Object>) currentOb;
      /*check  for key relation(int,int).
       * 
       */

      Pattern p = Pattern.compile("relation\\((\\w+),(\\w+)\\)");
      Matcher m = p.matcher((String) ent.getKey());
      /**If it matches set source and destination levels. 
       */
      if (m.matches()) {
        sourceLevel = LevelId.levelIdFor(m.group(1));
        destinationLevel = LevelId.levelIdFor(m.group(2));

      }
      /**Check for property name.
       * 
       */
      if (ent.getKey().equals("property")) {
        propertyName = (String) ent.getValue();
        if (sConversions == null) {
          sConversions = new LinkedHashMap<String, String>();
        }
        sConversions.put(propertyName, propertyName);
      }

      /**If value is string  add entry to sConversion .
       * 
       */

      else if (ent.getValue() instanceof String) {
        if (sConversions == null) {
          sConversions = new LinkedHashMap<String, String>();
        }
        sConversions.put((String) ent.getKey(),
            (String) ent.getValue());
      }
      /**If value is Transitions add entry to oConversions
       * 
       */
      else if (ent.getValue() instanceof Transitions) {
        if (oConversions == null) {
          oConversions = new LinkedHashMap<String, Transitions>();
        }
        oConversions.put((String) ent.getKey(), 
            (Transitions) ent.getValue());
      }
      /**Any other object as key should be parsed.
       * 
       */
      else {
        parse(ent.getValue());
      }
    }
    /**Map case.
     * 
     */
    else if (currentOb instanceof LinkedHashMap< ? , ? >) {
      /**Cast to map and loop through the values.
       * 
       */
      LinkedHashMap<Object, Object> map = 
        (LinkedHashMap<Object, Object>) currentOb;
      Set<Entry<Object, Object>> entries = map.entrySet();
      for (Entry<Object, Object> entry : entries ) {
        parse(entry);
      }
    }
    /**List case.
     * 
     */
    else if (currentOb instanceof ArrayList< ? >) {
      /**loop through list and parse each object. 
       * 
       */
      for (Object val : (ArrayList<Object>) currentOb){
        parse(val);
      }
    }
    else{
      System.out.println("unexpected object "
          + currentOb.toString()
          + " in Refinement Parse() method");
      throw new InvalidRefinementSpecificationException();
    }

  }
//  /**Check Validity Of RefinementProp.
//   * <p> Basic test to check that all variables are not null</p>
//   */
//  private boolean isValidRefinementProperty() {
//    if (propertyName == null || oConversions == null || sConversions == null) {
//      return false;
//    } else {
//      return true;
//    }
//  }
  
  /**Check if LevelRepresenation match p1 refines to p2.
   * @param p1 source property match to check.
   * @param p2 destination property to check.
   * @return true if p1 refines to p2.
   * @throws UnknownVariableIdentifierException 
   * @throws IncompatibleSemanticPropertyInstancesException 
   * @throws InvalidRefinementException 
   */
  public final boolean isValidRefinement(final SemanticPropertyInstance p1, final SemanticPropertyInstance p2) throws  IncompatibleSemanticPropertyInstancesException, InvalidRefinementException{
    /**
     * Check that p1 and p2 are right levels for this refinement.
     */
    if(!(sourceLevel == p1.getLevel() || destinationLevel == p2.getLevel())) {
      throw new IncompatibleSemanticPropertyInstancesException();
    }
    /**
     * Check all the capturing groups are refined.
     */
    String p1Match = p1.getInput();
    String p2Match = p2.getInput();
    Iterator<String> it = oConversions.keySet().iterator();
    while (it.hasNext()) {
      try {
        String presKey = (String) it.next();
        MyObject ob1 = (MyObject)p1.getVariable(presKey);
        MyObject ob2 = (MyObject)p2.getVariable(presKey);
        //check if p1 is a valid conversion for ob1. remove later
        if (ob1 == null) {
          return false;
        }
        //check the type of conversion
        Transitions tran = oConversions.get(presKey);
        //for string conversions
        if ((ob1 instanceof MyStringObject) && (ob2 instanceof MyStringObject)){
          String a = (String) ob1.getValue();
          String b = (String) ob2.getValue();
          //deal with each conversion appropriately
          if (tran.equals(Transitions.prefix)) { 
            if (!b.startsWith(a)) {
              throw new InvalidRefinementException();
            }
          }
          else if (tran.equals(Transitions.substring)) { 
            if (!b.contains(a)) {
              throw new InvalidRefinementException();
            }
          }
          else if (tran.equals(Transitions.suffix)) { 
            if (!b.endsWith(a)) {
              throw new InvalidRefinementException();
            }
          }
          else if (tran.equals(Transitions.equals)) { 
            if (!b.equals(a)) {
              throw new InvalidRefinementException();
            }
          }
          //adjust p1Match & p2Match based on MyObject kind
          if(ob1 instanceof MyString) {
            p1Match = p1Match.replace( "'" + a + "'", "");
            p2Match = p2Match.replace( "'" + b + "'", "");
          }
          
          if(ob1 instanceof MyDescription) {
            p1Match = p1Match.replace(  a + ".", "");
            p2Match = p2Match.replace(  b + ".", "");
          }
          if(ob1 instanceof MyExpression) {
            p1Match = p1Match.replace( "(" + a + ")", "");
            p2Match = p2Match.replace( "(" + b + ")", "");
          }
          
        }
      } catch(UnknownVariableIdentifierException e){
        //TODO
      }
    }
    /**Check all strings are refined.
     * 
     */
    StringTokenizer parser1 = new StringTokenizer(p1Match);
    StringTokenizer parser2 = new StringTokenizer(p2Match);
    while (parser1.hasMoreTokens()) {
      String i = parser1.nextToken();
      String j = parser2.nextToken();
      if (sConversions.containsKey(i)) {
        if (!j.equals(sConversions.get(i))) {
          return false;
        }
      } else {
        System.out.println("problem with " + i + " and " + j);
        return false;

      }

    }
    return true;  

  }


  /**Refine p1 based on rules in this Refinement LevelRepresenation.
   * 
   * @param p1 Source LevelRepresenation Match.
   * @return The refinement of p1 using this refinement property.
   * @param level the level to refine to.
   * @throws IncompatibleSemanticPropertyInstancesException 
   */
  public final SemanticPropertyInstance refine(final SemanticPropertyInstance  p1, LevelId level) throws IncompatibleSemanticPropertyInstancesException {
    /**
     * Check that p1 and p2 are right levels for this refinement.
     */
    if(!(sourceLevel == p1.getLevel()) || !(destinationLevel == level)) {
      throw new IncompatibleSemanticPropertyInstancesException();
     
    }
    HashMap<String,Object> newCaptured = new HashMap <String, Object> (); 
    
    /**
     * refine all the capturing groups are refined.
     */
    String p1Match = p1.getInput();
    String newInput = p1.getInput();
    Iterator<String> it = oConversions.keySet().iterator();
    while (it.hasNext()) {
      try {
        String presKey = (String) it.next();
        Object ob1 = (Object)p1.getVariable(presKey);

        //check the type of conversion
        Transitions tran = oConversions.get(presKey);
        //for string conversions
        if ((ob1 instanceof String)){
          String a = (String) ob1;
          String newa="";
          //deal with each conversion appropriately
          if (tran.equals(Transitions.prefix)) { 
            newa=a+" extra";
          }
          else if (tran.equals(Transitions.substring)) { 
            
          }
          else if (tran.equals(Transitions.suffix)) { 
            newa="extra "+ a;
          }
          //adjust p1Match & p2Match
          newCaptured.put(presKey,newa);
          p1Match = p1Match.replace("'"+a+"'", "");
          
          newInput = newInput.replace( a , newa);
        }
      } catch(UnknownVariableIdentifierException e){
        
      }
    }
    /**refine all strings.
     * 
     */
    StringTokenizer parser1 = new StringTokenizer(p1Match);
    while (parser1.hasMoreTokens()) {
      String i = parser1.nextToken();
      if (sConversions.containsKey(i)) {
        p1Match = p1Match.replace(i, "");
        newInput = newInput.replace(i, sConversions.get(i));
      } else {
        System.out.println("problem with " + i );

      }

    }
    if(p1Match.equals("")){
      
    }
    return new SemanticPropertyInstance(newInput,p1.getPropertyType(),level,p1.getScope(),newCaptured);

  }
  /**Getters.
   * 
   */

  /**
   * @return the sConversions.
   */
  public final LinkedHashMap<String, String> getSConversions() {
    return sConversions;
  }
  /**
   * @return the oConversions
   */
  public final LinkedHashMap<String, Transitions> getOConversions() {
    return oConversions;
  }
  /**
   * @return the sourceLevel
   */
  public final LevelId getSourceLevel() {
    return sourceLevel;
  }
  /**
   * @return the destinationLevel
   */
  public final LevelId getDestinationLevel() {
    return destinationLevel;
  }

}
