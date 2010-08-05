package ie.ucd.semanticproperties.plugin.api;

import ie.ucd.semanticproperties.plugin.exceptions.UnknownVariableIdentifierException;
import java.util.ArrayList;
import java.util.HashMap;

/**
 * An input matched against a semantic property.
 * @author eo
 *
 */
public class SemanticPropertyInstance {
  /**
   * The level of this instance.
   */
  private LevelId level;
  /**
   * The scope that this instance covers.
   */
  private ArrayList<ScopeId> scope;
  /**
   * The name of the semantic property that this is an instance of.
   */
  private String propId;
  /**
   * HashMap of the captured objects and their names as keys.
   */
  private HashMap<String,Object> captured;

  /**
   * Constructor for a new instance.
   * @param name The semantic of new instance.
   * @param level The level of the new instance.
   * @param scope The scope for new instance to cover.
   * @param map The map of objects for new instance
   */
  public SemanticPropertyInstance(String name, LevelId level, ArrayList<ScopeId> scope,HashMap<String, Object> map) {
    /**
     * Assign scope, level and Id.
     */
    this.scope = scope;
    this.level = level;
    this.propId = name;
    this.captured = map;
  }

  /**
   * Get the semantic property that this is an instance of.
   * @return The semantic property for this instance.
   */
  public String getPropertyType() {
    return propId;
  }
  /**
   * Get the object that was captured for this name.
   * @param identifier Name of object to return.
   * @return The object for this name.
   * @throws UnknownVariableIdentifierException When no variable exists for this name.
   */
  public Object getVariable(String identifier) throws UnknownVariableIdentifierException {
    if(captured.containsKey(identifier)){
      return captured.get(identifier);
    } else{
      throw new UnknownVariableIdentifierException();
    }
  }
  /**
   * Get the int that was captured for this name.If not an int throws an error.
   * @param identifier Name of object to return.
   * @return The object for this name.
   * @throws UnknownVariableIdentifierException When no variable exists for this name.
   */
  public int getIntVariable(String identifier) throws UnknownVariableIdentifierException {
    if(captured.containsKey(identifier)){
      Object toCheck = captured.get(identifier);
      if(toCheck instanceof Integer){
        return ((Number)toCheck).intValue();
      }
      else{
        throw new  UnknownVariableIdentifierException();
      }
      
    } else{
      throw new UnknownVariableIdentifierException();
    }
  }
  

  //TODO
  //public int getIntVariable(String identifier) throws UnknownVariableIdentifierException {

  /**
   * Get the level for this instance.
   * @return The LevelId for this instance.
   */
  public LevelId getLevel() {
    return level;
  }
  /**
   * Get the scope for this instance.
   * @return the scopeId for this instance.
   */
  public ArrayList<ScopeId> getScope() {
    return scope;
  }
  /**
   * Produce a string representation of this semantic property instance.
   * This essentially is a pretty print of the contained data, with knowledge
   * of the semantic property's format.
   */
  public String toString() {
    return null;
  }


}
