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
import ie.ucd.semanticproperties.plugin.structs.SemanticPropertyLevelSpecification;
import ie.ucd.semanticproperties.plugin.structs.SemanticProperty;
import ie.ucd.semanticproperties.plugin.structs.SemanticPropertyRefinementSpecification;

import java.io.File;
import java.io.FileNotFoundException;
import java.io.IOException;
import java.util.ArrayList;
import java.util.HashMap;

public class SemanticPropertiesHandler {

  private final  ArrayList<SemanticProperty> specs;
  private final HashMap<String,SemanticProperty> specsMap ;
  
  public SemanticPropertiesHandler() {
    specs =  new ArrayList<SemanticProperty>();
    specsMap = new HashMap<String , SemanticProperty>();
  }

  /**
   * Parse the provided input file and add the property specification contained
   * within the the set of known properties.
   * @param propertySpecFile
   * @throws IOException 
   */
  public void add(File propertySpecFile) throws InvalidSemanticPropertySpecificationException, IOException {
    SemanticProperty temp = new SemanticProperty(propertySpecFile);
    specs.add(temp);
    specsMap.put(temp.getName(),temp);
  }

  /**
   * Parse the given input string using the set of known semantic properties.
   * 
   * @param input
   * @param scope
   * @param level
   * @return
   */
  public SemanticPropertyInstance parse(String input, String name, LevelId level) 
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
   * Checks if two semantic property instances are a valid refinement, according to
   * the refinement specification for the corresponding semantic property.
   * 
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
   */
  public SemanticPropertyInstance generate(SemanticPropertyInstance  input, LevelId level)
    throws UnknownLevelException, IncompatibleSemanticPropertyInstancesException {
    SemanticProperty temp = specsMap.get(input.getPropertyType());
    SemanticPropertyRefinementSpecification ref =temp.getRefinement(input.getLevel(), level);

    return ref.refine(input,level);
  }

}
