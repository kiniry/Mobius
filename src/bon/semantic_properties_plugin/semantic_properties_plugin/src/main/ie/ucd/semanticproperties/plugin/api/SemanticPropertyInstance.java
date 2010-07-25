package ie.ucd.semanticproperties.plugin.api;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import ie.ucd.semanticproperties.plugin.customobjects.MyObject;
import ie.ucd.semanticproperties.plugin.exceptions.UnknownVariableIdentifierException;
import ie.ucd.semanticproperties.plugin.structs.SemanticPropertyLevelSpecification;
import ie.ucd.semanticproperties.plugin.structs.RegExpStruct;

public class SemanticPropertyInstance {
  
  private LevelId level;
  private ArrayList<ScopeId> scope;
  private String propId;
  private HashMap<String,Object> captured; 
  private String input;
  //TODO args to constructor (Map<String,?>,propId,scope,level)
  //scope might not be needed
  public SemanticPropertyInstance(String input, String name, LevelId level, ArrayList<ScopeId> scope,HashMap<String, Object> map) {
    /**
     * Assign scope, level and Id.
     */
    this.input=input;
    this.scope = scope;
    this.level = level;
    this.propId = name;
    this.captured = map;
    
  }

  public String getPropertyType() {
    return propId;
  }
  public Object getVariable(String identifier) throws UnknownVariableIdentifierException {
    if(captured.containsKey(identifier)){
      return captured.get(identifier);
    } else{
      throw new UnknownVariableIdentifierException();
    }
  }

  //TODO
  //public int getIntVariable(String identifier) throws UnknownVariableIdentifierException {

  public LevelId getLevel() {
    return level;
  }

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

  public HashMap<String, Object> getCaptured() {
    return captured;
  }

  public String getInput() {
    return input;
  }

}
