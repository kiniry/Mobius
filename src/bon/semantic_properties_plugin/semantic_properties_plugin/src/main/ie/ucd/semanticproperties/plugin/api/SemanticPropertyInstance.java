package ie.ucd.semanticproperties.plugin.api;

import ie.ucd.semanticproperties.plugin.exceptions.UnknownVariableIdentifierException;

public class SemanticPropertyInstance {

  //TODO args to constructor (Map<String,?>,propId,scope,level)
  public SemanticPropertyInstance() {
    //TODO
  }
  
  public String getPropertyType() {
    return null;
  }
  
  public Object getVariable(String identifier) throws UnknownVariableIdentifierException {
    //TODO
    return null;
  }
  
  //TODO
  //public int getIntVariable(String identifier) throws UnknownVariableIdentifierException {
  
  public LevelId getLevel() {
    return null;
  }
  
  public ScopeId getScope() {
    return null;
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
