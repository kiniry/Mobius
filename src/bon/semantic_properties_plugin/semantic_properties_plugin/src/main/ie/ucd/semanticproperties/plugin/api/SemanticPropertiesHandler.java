package ie.ucd.semanticproperties.plugin.api;

import ie.ucd.semanticproperties.plugin.exceptions.IncompatibleSemanticPropertyInstancesException;
import ie.ucd.semanticproperties.plugin.exceptions.InvalidSemanticPropertySpecificationException;
import ie.ucd.semanticproperties.plugin.exceptions.InvalidSemanticPropertyUseException;
import ie.ucd.semanticproperties.plugin.exceptions.SemanticPropertyNotValidAtScopeException;
import ie.ucd.semanticproperties.plugin.exceptions.UnknownLevelException;
import ie.ucd.semanticproperties.plugin.exceptions.UnknownPropertyException;
import ie.ucd.semanticproperties.plugin.exceptions.UnknownScopeException;

import java.io.File;
import java.io.FileNotFoundException;

public class SemanticPropertiesHandler {

  //private final specs List<SemanticPropertySpecification>;
  //private final specsMap Map<String,SemanticPropertySpecification>
  
  public SemanticPropertiesHandler() {
    //TODO
  }

  /**
   * Parse the provided input file and add the property specification contained
   * within the the set of known properties.
   * @param propertySpecFile
   */
  public void add(File propertySpecFile) throws FileNotFoundException, InvalidSemanticPropertySpecificationException {
    //TODO
  }

  /**
   * Parse the given input string using the set of known semantic properties.
   * 
   * @param input
   * @param scope
   * @param level
   * @return
   */
  public SemanticPropertyInstance parse(String input, ScopeId scope, LevelId level) 
    throws UnknownPropertyException, InvalidSemanticPropertyUseException,
           UnknownLevelException, UnknownScopeException, SemanticPropertyNotValidAtScopeException {
    //TODO
    return null;
  }

  /**
   * Checks if two semantic property instances are a valid refinement, according to
   * the refinement specification for the corresponding semantic property.
   * 
   * @param prop1
   * @param prop2
   * @return
   */
  public boolean isValidRefinement(SemanticPropertyInstance prop1, SemanticPropertyInstance prop2) 
    throws IncompatibleSemanticPropertyInstancesException {
    //TODO
    return false;
  }

  /**
   * Perform refinement on the given semantic property instance, production a new semantic property 
   * instance at the given level.
   * @param input
   * @param level
   * @return
   */
  public SemanticPropertyInstance generate(SemanticPropertyInstance  input, LevelId level)
    throws UnknownLevelException, IncompatibleSemanticPropertyInstancesException {
    //TODO
    return null;
  }

}
