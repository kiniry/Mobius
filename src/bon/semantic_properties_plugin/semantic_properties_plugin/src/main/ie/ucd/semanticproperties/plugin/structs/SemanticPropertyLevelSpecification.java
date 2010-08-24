
/**
 * @title "Semantic LevelRepresenation Plugin Package"
 * @description "Class that represents,checks and generates a regexp for a semantic property."
 * @author  Eoin O'Connor
 * @copyright ""
 * @license "Public Domain."
 * @version "$Id: 01-07-2010 $"
 */

package ie.ucd.semanticproperties.plugin.structs;

import ie.ucd.semanticproperties.plugin.api.LevelId;
import ie.ucd.semanticproperties.plugin.api.ScopeId;
import ie.ucd.semanticproperties.plugin.api.SemanticPropertyInstance;
import ie.ucd.semanticproperties.plugin.customobjects.Keyword;
import ie.ucd.semanticproperties.plugin.customobjects.MyObject;
import ie.ucd.semanticproperties.plugin.exceptions.InvalidLevelSpecificationException;
import ie.ucd.semanticproperties.plugin.exceptions.InvalidSemanticPropertySpecificationException;
import ie.ucd.semanticproperties.plugin.exceptions.InvalidSemanticPropertyUseException;
import ie.ucd.semanticproperties.plugin.exceptions.UndefinedLevelException;
import ie.ucd.semanticproperties.plugin.exceptions.UndefinedScopeException;
import ie.ucd.semanticproperties.plugin.yaml.CustomConstructor;
import ie.ucd.semanticproperties.plugin.yaml.CustomRepresenter;
import ie.ucd.semanticproperties.plugin.yaml.CustomResolver;

import java.io.File;
import java.io.FileInputStream;
import java.io.IOException;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.Set;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import org.antlr.stringtemplate.StringTemplate;
import org.antlr.stringtemplate.language.DefaultTemplateLexer;
import org.yaml.snakeyaml.Dumper;
import org.yaml.snakeyaml.DumperOptions;
import org.yaml.snakeyaml.Loader;
import org.yaml.snakeyaml.Yaml;

/**
 * A class representing a semantic property.
 * <p>
 * A class representing a semantic property that consists of
 * format,name,scope,description and a regular expression structure.
 * </p>
 * 
 * @see RegExpStruct
 * @version "$Id: 01-07-2010 $"
 * @author Eoin O'Connor
 */

public class SemanticPropertyLevelSpecification {

  /**
   * Strings Used for Validity Checks.
   * Definition of what makes an acceptable property for name,scope,description
   * and the different format possibilities
   */
  final static String prop_Scope = "(files|modules|features|variables|all|special)";
  final static String prop_Description = ".*";
  final static String prop_format_String = "(\\w*)";
  final static String prop_format_CustomObject = "(\\w+=(.)*)";
  final static String prop_format_Keyword = "(\\w+=\\w+)";
  final static String prop_format_Special = "((choice\\s*\\((\\w+)\\)\\s*)|choice|optional)";
  final static String prop_Name = "\\s*\\w+\\s*";
  final static String prop_Level = "[=-]?\\d+";

  /**
   * The variables for a property.
   * <p>
   * list of property attributes
   * </p>
   */
  private static ArrayList<Object> format;
  private static ArrayList<ScopeId> scope;
  private static String description;
  private static String name;
  private LevelId level;
  private RegExpStruct reg;

  /**
   * Constructor for linkedHashMap.
   * 
   * @param input
   *          linkedHashMap with property in it.
   * @throws UndefinedScopeException 
   * @throws InvalidSemanticPropertySpecificationException
   */
  public SemanticPropertyLevelSpecification(final LinkedHashMap<String, ?> input)
      throws InvalidLevelSpecificationException, UndefinedScopeException {
    parse(input);
  }
  
    
  /**
   * Constructor for yaml file.
   * 
   * @param input
   *          Yaml file to parse.
   * @throws InvalidSemanticPropertySpecificationException
   * @throws IOException
   * @throws UndefinedScopeException 
   */
  @SuppressWarnings("unchecked")
  public SemanticPropertyLevelSpecification(File input) throws InvalidLevelSpecificationException, IOException, UndefinedScopeException {
    Yaml yaml = new Yaml(new Loader(new CustomConstructor()), new Dumper(new CustomRepresenter(), new DumperOptions()), new CustomResolver());
    FileInputStream io = new FileInputStream(input);
    Object ob = yaml.load(io);
    parse((LinkedHashMap<String, ?>) ob);
  }
//
///**
// * Constructor for string with yaml content.
// * 
// * @param input
// *          Constructor for yaml file.
// * @throws InvalidSemanticPropertySpecificationException
// */
//@SuppressWarnings("unchecked")
//public SemanticPropertyLevelSpecification(String input)
//    throws InvalidSemanticPropertySpecificationException {
//  Yaml yaml = new Yaml(new Loader(new CustomConstructor()), new Dumper(
//      new CustomRepresenter(), new DumperOptions()), new CustomResolver());
//  Object ob = yaml.load(input);
//  parse((LinkedHashMap<String, ?>) ob);
//
//}
  /**
   * parse method for LinkedHashMap.
   * <p>
   * method takes in snakyaml parsed linkedHashMap and fills this property's
   * values
   * </p>
   * 
   * @param linkedHashMap
   *          to parse
   * @throws UndefinedScopeException 
   * @throws InvalidSemanticPropertySpecificationException
   */

  @SuppressWarnings("unchecked")
  private void parse(LinkedHashMap<String, ?> linkedHashMap) throws InvalidLevelSpecificationException, UndefinedScopeException {

    checkValidity(linkedHashMap);

    name = (String) linkedHashMap.get("name");
    format = (ArrayList<Object>) linkedHashMap.get("format");
    description = (String) linkedHashMap.get("description");
    /**
     * get scopes
     */
    ArrayList<String> stringScopes = (ArrayList<String>) linkedHashMap.get("scope");
    scope = new ArrayList<ScopeId>();
    for (String s : stringScopes) {
      /**
       * Check validity of scope.
       */
        scope.add(ScopeId.scopeIdFor(s));
    
    }
    /**
     * Generate regExpStruct
     */
    reg = generateRegExp();
    /**
     * Get level and check that it is valid.
     */
    try {
      level = LevelId.levelIdFor((String) linkedHashMap.get("level"));
    }catch( UndefinedLevelException e){
      throw new InvalidLevelSpecificationException();
    }
  }

  /**
   * <p>Review how much is necessary.
   * Checks prop for validity based on the definition in the strings at the
   * beginning of this file
   * </p>
   * 
   * @param newProp
   *          linkedHashMap that contains potential property as parsed by
   *          snakeyaml
   * @return true when the property is valid.
   */
  private void checkValidity(final LinkedHashMap<String, ?> newProp)
      throws InvalidLevelSpecificationException {


    /**
     * Check the name.
     */
    Pattern namePattern = Pattern.compile(prop_Name);
    Matcher nameMatcher = namePattern.matcher((String) newProp.get("name"));
    if (!nameMatcher.matches()) {
      throw new InvalidLevelSpecificationException();

    }

    /**
     * Check the description.
     */
    Pattern descriptionPattern = Pattern.compile(prop_Description,Pattern.DOTALL);
    Matcher descriptionMatcher = descriptionPattern.matcher((String) newProp.get("description"));
    if (!descriptionMatcher.matches()) {
      throw new InvalidLevelSpecificationException();
    }

    /**
     * Check the format with recursive method.
     */
    checkFormatValidity((ArrayList<Object>) newProp.get("format"));
  }

  /**
   * recursive method to check if object is a valid format property.
   * @param formatValue Object to be checked
   * @return true when object is a valid format object.
   */

  private void checkFormatValidity(Object formatValue)
      throws InvalidLevelSpecificationException {

    /**
     * String case.
     */
    if (formatValue instanceof String) {
      Pattern formatPattern = Pattern.compile(prop_format_String);
      Matcher nameMatcher = formatPattern.matcher((String) formatValue);
      if (!nameMatcher.matches()) {
        throw new InvalidLevelSpecificationException();
      }
    }
    /**
     * List Case
     */
    else if (formatValue instanceof ArrayList<?>) {
      /**
       * check all objects in list.
       */
      for (Object optionalNameValue : (ArrayList<?>) formatValue) {
          checkFormatValidity(optionalNameValue);
      }
    }
    /**
     * LinkedHashMap Case.
     */
    else if (formatValue instanceof LinkedHashMap<?, ?>) {
      // checks if formatVlaue is an instance of optional: or choice:


      Pattern formatPattern = Pattern.compile(prop_format_Special);
      LinkedHashMap<String, ?> r = (LinkedHashMap<String, ?>) formatValue;
      // loop through all keys
      Set<String> keys = r.keySet();
      for (String s : keys) {
        Matcher nameMatcher = formatPattern.matcher(s);
        if (nameMatcher.matches()) {
          checkFormatValidity(r.get(s));
        } else {
          throw new InvalidLevelSpecificationException();
        }
      }
    }
    /**
     * Custom Object Case.
     */
    else if (formatValue instanceof MyObject) {

      Pattern formatPattern = Pattern.compile(prop_format_CustomObject);
      Matcher nameMatcher = formatPattern.matcher(((MyObject) formatValue).toString());
      if (!nameMatcher.matches()) {
        throw new InvalidLevelSpecificationException();
      }
    }
    /**
     * Keyword Case.
     */
    else if (formatValue instanceof Keyword){
      Pattern formatPattern = Pattern.compile(prop_format_Keyword);
      Matcher nameMatcher = formatPattern.matcher(((Keyword) formatValue)
          .toString());
      if (!nameMatcher.matches()) {
        throw new InvalidLevelSpecificationException();
      }
    }
    /**
     * Unknown Object Case.
     */
    else {
      throw new InvalidLevelSpecificationException();
    }
  }

  /**
   * Build a RegExpStruct for property.
   * 
   * @return RegExpStruct representation of property
   * @throws InvalidSemanticPropertySpecificationException
   */

  private static RegExpStruct generateRegExp() throws InvalidLevelSpecificationException {
    return generateRegExp(format);
  }

  /**
   * Recursive method to build RegeExpStruct for an object
   * 
   * @param ob
   *          object to generate RegExpStruct from
   * @return RegExpStruct representation of object
   * @throws InvalidSemanticPropertySpecificationException
   */

  private static RegExpStruct generateRegExp(Object ob) throws InvalidLevelSpecificationException {
    
    //ArrayList Case.
    if (ob instanceof ArrayList<?>) {
      // cast to list
      ArrayList<?> list = (ArrayList<?>) ob;
      // Create RegExpStruct and add on RegExpStruct for each item.
      RegExpStruct listReg = new RegExpStruct();
      for (Object obin : list) {
        RegExpStruct temp = generateRegExp(obin);
        listReg.add(temp);
      }
      return listReg;
    
    }
    // Map case.
    else if (ob instanceof LinkedHashMap<?, ?>) {
      // Cast ob to LinkeHashMap.
      LinkedHashMap<String, ?> all = (LinkedHashMap<String, ?>) ob;
      // RegExpStruct list = new RegExpStruct();

      // choice sub case.
      if (all.containsKey("choice")) {
        RegExpStruct choice = new RegExpStruct(RegType.CHOICE);
        /**
         * Get list of choices
         */
        ArrayList<?> choices = (ArrayList<?>) all.get("choice");
        /**
         * Loop through list choices and build RegExpStruct.
         */
        for (Object obin : choices) {
          RegExpStruct temp = generateRegExp(obin);
          choice.add(temp);
        }
        return choice;
      }
      // optional sub case
      else if (all.containsKey("optional")) {
        RegExpStruct opt = new RegExpStruct(RegType.OPTIONAL);
        Object optionOb = all.get("optional");
        RegExpStruct optionalReg = generateRegExp(optionOb);
        opt.add(optionalReg);
        return opt;

      }
      // return list;
    }

    // String case.
    else if (ob instanceof String) {
      return new RegExpStruct(ob);
    }
    // MyObject case.
    else if (ob instanceof MyObject) {
      return new RegExpStruct(ob);
    }
    
    else if (ob instanceof Keyword) {
      return new RegExpStruct(ob);
    }
    
    //Any unacceptable type.
    throw new InvalidLevelSpecificationException();
  }

  /**
   * generate SPI from input for this specification.
   * 
   * @return
   * @throws InvalidSemanticPropertyUseException
   */
  public SemanticPropertyInstance makeInstance(String input)
      throws InvalidSemanticPropertyUseException {
    HashMap<String, Object> captured = reg.match(input);
    return new SemanticPropertyInstance(name, level, scope, captured, this.getPrettyPrint());
  
  }

  /**
   * @return
   */
  public StringTemplate getPrettyPrint() {
    String i = this.name;
    LinkedHashMap<String, Object> te = reg.getGroupObj();
    for (String key : te.keySet()) {
      i += ("$" + key + "$");
    }
    return new StringTemplate(i, DefaultTemplateLexer.class);
  }

  /**
   * Gets the regular expression for this property.
   * 
   * @return RegExpStruct representation of this property
   */
  public RegExpStruct getReg() {
    return reg;
  }

  public String getName() {
    return name;
  }

  public ArrayList<ScopeId> getScope() {
    return scope;
  }

  public void setScope(ArrayList<ScopeId> scope) {
    SemanticPropertyLevelSpecification.scope = scope;
  }

  public LevelId getLevel() {
    return level;
  }

}
