package ie.ucd.semanticproperties.plugin.api;

import ie.ucd.semanticproperties.plugin.exceptions.IncompatibleSemanticPropertyInstancesException;
import ie.ucd.semanticproperties.plugin.exceptions.InvalidRefinementException;
import ie.ucd.semanticproperties.plugin.exceptions.InvalidSemanticPropertySpecificationException;
import ie.ucd.semanticproperties.plugin.exceptions.InvalidSemanticPropertyUseException;
import ie.ucd.semanticproperties.plugin.exceptions.UndefinedLevelException;
import ie.ucd.semanticproperties.plugin.exceptions.UnknownPropertyException;
import ie.ucd.semanticproperties.plugin.exceptions.UndefinedScopeException;
import ie.ucd.semanticproperties.plugin.exceptions.UnknownVariableIdentifierException;
import ie.ucd.semanticproperties.plugin.structs.SemanticProperty;
import ie.ucd.semanticproperties.plugin.structs.SemanticPropertyLevelSpecification;
import ie.ucd.semanticproperties.plugin.structs.SemanticPropertyRefinementSpecification;
import java.io.File;
import java.io.IOException;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

/**
 * Class that holds semantic properties and can create and check instances.
 * @author Eoin O'Connor
 *
 */
public class SemanticPropertiesHandler {

  /**
   * HashMap of semantic properties names as key and the semantic properties themselves as values.
   */
  private final HashMap<String,SemanticProperty> specsMap;
  /**
   * Default Constructor.
   * Makes new Handler with no semantic properties.
   */
  public SemanticPropertiesHandler() {
    specsMap = new HashMap<String , SemanticProperty>();
  }

  /**
   * Adds the semantic property specification contained in yaml file.
   * The File should be of the correct form or an exception will be thrown.
   * @param propertySpecFile The yaml file representing semantic property to add.
   * @throws InvalidSemanticPropertySpecificationException If file dosn't contain valid semantic property.
   * @throws IOException If file dosn't exist.
   */
  public final void add(final File propertySpecFile) throws InvalidSemanticPropertySpecificationException, IOException {
    SemanticProperty temp = new SemanticProperty(propertySpecFile);
    specsMap.put(temp.getName(),temp);
  }

  /**
   * Create SemanticPropertyInstance for this input at tjis level for single scope.
   * @param input String to create instance for.
   * @param name Name of semantic property to create instance for.
   * @param level The level to create instance for.
   * @return new SemanticPropertyInstance for this input string.
   * @throws UnknownPropertyException
   * @throws InvalidSemanticPropertyUseException
   * @throws UndefinedLevelException
   * @throws UndefinedScopeException
   * @throws SemanticPropertyNotValidAtScopeException
   */
  public final SemanticPropertyInstance parse(String input, String name, LevelId level,ScopeId scope) 
    throws UnknownPropertyException, InvalidSemanticPropertyUseException,
           UndefinedLevelException, UndefinedScopeException {
    /**
     * Check that this Handler has semantic property for this name.
     */
    SemanticProperty temp = specsMap.get(name);
    if(temp==null) {
      throw new UnknownPropertyException();
    }
    /**
     * Check that level exists for this semantic property.
     */
    SemanticPropertyLevelSpecification lev = temp.getLevels().get(level);
    if(lev==null){
      throw new UndefinedLevelException();
    }
    /**
     * Check that the scope is valid.
     */
    ArrayList<ScopeId> levScope= lev.getScope();
      if(!levScope.contains(scope)){
        throw new UndefinedScopeException();
      }

    SemanticPropertyInstance i = lev.makeInstance(input);
    return i;
  }
  /**
   * Create SemanticPropertyInstance for this input at this level for single scope.
   * @param input String to create instance for.
   * @param name Name of semantic property to create instance for.
   * @param level The level to create instance for.
   * @return new SemanticPropertyInstance for this input string.
   * @throws UnknownPropertyException
   * @throws InvalidSemanticPropertyUseException
   * @throws UndefinedLevelException
   * @throws UndefinedScopeException
   * @throws SemanticPropertyNotValidAtScopeException
   */
  public final SemanticPropertyInstance parse(String input,LevelId level,ScopeId scope) 
    throws UnknownPropertyException, InvalidSemanticPropertyUseException,
           UndefinedLevelException, UndefinedScopeException {
    /**
     * Extract property name from input.
     */
    Pattern p = Pattern.compile("(\\w*).+");
    Matcher m = p.matcher(input);
    m.matches();
    /**
     * Check that Handler has semantic property for input name.
     */
    SemanticProperty temp = specsMap.get(m.group(1));
    if(temp==null) {
      throw new UnknownPropertyException();
    }
    /**
     * Check that level exists for this semantic property.
     */
    SemanticPropertyLevelSpecification lev = temp.getLevels().get(level);
    if(lev==null){
      throw new UndefinedLevelException();
    }
    /**
     * Check that scope is valid.
     */
    ArrayList<ScopeId> levScope= lev.getScope();
      if(!levScope.contains(scope)){
        throw new UndefinedScopeException();
      }
    /**
     * remove property name from input
     */
    String toRemove = m.group(1);
    input=input.substring(toRemove.length()+1 ,input.length());
    /**
     * Create and return instance for the input string.
     */
    SemanticPropertyInstance i = lev.makeInstance(input);
    return i;
  }

  /**
   * Checks if a semantic property instances refines to another for this handler.
   * Uses the refinement specification for the correct semantic property.
   * @param prop1
   * @param prop2
   * @return true if valid refinement.
   * @throws IncompatibleSemanticPropertyInstancesException
   * ask fintan
   * @throws UnknownVariableIdentifierException
   * 
   * @throws InvalidRefinementException
   * @throws UnknownPropertyException
   * @throws UndefinedLevelException
   */
  public boolean isValidRefinement(SemanticPropertyInstance prop1, SemanticPropertyInstance prop2)
    throws IncompatibleSemanticPropertyInstancesException, UnknownVariableIdentifierException, InvalidRefinementException, UnknownPropertyException, UndefinedLevelException {
    /**
     * Check that both instances belong to same Semantic Property
     */
    if(prop1.getPropertyType() != prop2.getPropertyType()){
      throw new IncompatibleSemanticPropertyInstancesException();
    }
    /**
     * Check the semantic property.
     */
    SemanticProperty mainSP = specsMap.get(prop1.getPropertyType());
    if(mainSP==null){
      throw new UnknownPropertyException();
    }
    /**
     * Check refinement for these two instances
     */
    SemanticPropertyRefinementSpecification ref = mainSP.getRefinement(prop1, prop2);
    /**
     * Check levels for the two instances
     */
    SemanticPropertyLevelSpecification propLev1 = mainSP.getLevels().get(prop1.getLevel());
    SemanticPropertyLevelSpecification propLev2 = mainSP.getLevels().get(prop2.getLevel());
    if(propLev1 == null || propLev2 == null){
      throw new UndefinedLevelException();
    }
    /**
     * Check refinement.
     */
    return ref.isValidRefinement(prop1, prop2, propLev1, propLev2);
  }

  /**
   * Perform refinement on the given semantic property instance, production a new semantic property.
   * instance at the given level.
   * @param input
   * @param level
   * @return generated SemanticPropertyInstance.
   * @throws InvalidRefinementException
   * @throws UnknownPropertyException
   */
  public SemanticPropertyInstance generate(SemanticPropertyInstance  input, LevelId level)
    throws UndefinedLevelException, IncompatibleSemanticPropertyInstancesException, InvalidRefinementException, UnknownPropertyException {
    /**
     * Check the semantic property.
     */
    SemanticProperty mainSP = specsMap.get(input.getPropertyType());
    if(mainSP==null){
      throw new UnknownPropertyException();
    }
    /**
     * Check refinement for these two instances
     */
    SemanticPropertyRefinementSpecification ref = mainSP.getRefinement(input.getLevel(), level);
    if(ref==null){
      throw new InvalidRefinementException();
    }
    /**
     * Check level.
     */
    SemanticPropertyLevelSpecification propLev = mainSP.getLevels().get(input.getLevel());
    if(propLev == null){
      throw new UndefinedLevelException();
    }
    /**
     * Generate refinement.
     */
    return ref.refine(input,level,propLev);
  }

}
