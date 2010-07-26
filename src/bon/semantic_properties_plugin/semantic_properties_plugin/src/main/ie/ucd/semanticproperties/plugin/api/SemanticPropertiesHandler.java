package ie.ucd.semanticproperties.plugin.api;

import ie.ucd.semanticproperties.plugin.exceptions.IncompatibleSemanticPropertyInstancesException;
import ie.ucd.semanticproperties.plugin.exceptions.InvalidRefinementException;
import ie.ucd.semanticproperties.plugin.exceptions.InvalidSemanticPropertySpecificationException;
import ie.ucd.semanticproperties.plugin.exceptions.InvalidSemanticPropertyUseException;
import ie.ucd.semanticproperties.plugin.exceptions.SemanticPropertyNotValidAtScopeException;
import ie.ucd.semanticproperties.plugin.exceptions.UnknownLevelException;
import ie.ucd.semanticproperties.plugin.exceptions.UnknownPropertyException;
import ie.ucd.semanticproperties.plugin.exceptions.UnknownScopeException;
import ie.ucd.semanticproperties.plugin.exceptions.UnknownVariableIdentifierException;
import ie.ucd.semanticproperties.plugin.structs.SemanticProperty;
import ie.ucd.semanticproperties.plugin.structs.SemanticPropertyLevelSpecification;
import ie.ucd.semanticproperties.plugin.structs.SemanticPropertyRefinementSpecification;
import java.io.File;
import java.io.IOException;
import java.util.ArrayList;
import java.util.HashMap;

/**
 * Class that allows a user to  add semantic property representations and instances.
 * @author Eoin O'Connor
 *
 */
public class SemanticPropertiesHandler {
  /**
   * The list of all the semantic properties for this handler.
   */
  private final ArrayList<SemanticProperty> specs;
  /**
   * HashMap of semantic properties names as key and the semantic properties themselves as values.
   */
  private final HashMap<String,SemanticProperty> specsMap;
  /**
   * Default Constructor.
   * <p> Makes new Handler with no semantic properties.
   */
  public SemanticPropertiesHandler() {
    specs =  new ArrayList<SemanticProperty>();
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
    specs.add(temp);
    specsMap.put(temp.getName(),temp);
  }

  /**
   * Create SemanticPropertyInstance for this input.
   * @param input String to create instance for.
   * @param name Name of semantic property to create instance for.
   * @param level The level to create instance for.
   * @return new SemanticPropertyInstance for this input string.
   */
  public final SemanticPropertyInstance parse(String input, String name, LevelId level) 
    throws UnknownPropertyException, InvalidSemanticPropertyUseException,
           UnknownLevelException, UnknownScopeException, SemanticPropertyNotValidAtScopeException {
    SemanticProperty temp = specsMap.get(name);
    if(temp==null) {
      throw new UnknownPropertyException();
    }
    SemanticPropertyLevelSpecification lev = temp.getLevels().get(level);
    if(lev==null){
      throw new UnknownLevelException();
    }
    SemanticPropertyInstance i = lev.makeInstance(input);
    return i;
  }

  /**
   * Checks if a semantic property instances refines to another for this handler.
   * Uses the refinement specification for the correct semantic property.
   * @param prop1
   * @param prop2
   * @return
   * review this throws
   * @throws UnknownVariableIdentifierException 
   * @throws InvalidRefinementException 
   */
  public boolean isValidRefinement(SemanticPropertyInstance prop1, SemanticPropertyInstance prop2) 
    throws IncompatibleSemanticPropertyInstancesException, UnknownVariableIdentifierException, InvalidRefinementException {
    //double done possibly.
    if(prop1.getPropertyType() != prop2.getPropertyType()){
      throw new IncompatibleSemanticPropertyInstancesException();
    }
    SemanticProperty temp = specsMap.get(prop1.getPropertyType());
    SemanticPropertyRefinementSpecification ref =temp.getRefinement(prop1, prop2);
    return ref.isValidRefinement(prop1, prop2);
  }

  /**
   * Perform refinement on the given semantic property instance, production a new semantic property 
   * instance at the given level.
   * @param input
   * @param level
   * @return
   * @throws InvalidRefinementException 
   */
  public SemanticPropertyInstance generate(SemanticPropertyInstance  input, LevelId level)
    throws UnknownLevelException, IncompatibleSemanticPropertyInstancesException, InvalidRefinementException {
    SemanticProperty temp = specsMap.get(input.getPropertyType());
    SemanticPropertyRefinementSpecification ref =temp.getRefinement(input.getLevel(), level);

    return ref.refine(input,level);
  }

}
