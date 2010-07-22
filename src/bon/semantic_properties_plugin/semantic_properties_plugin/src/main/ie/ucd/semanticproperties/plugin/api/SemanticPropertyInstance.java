package ie.ucd.semanticproperties.plugin.api;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import ie.ucd.semanticproperties.plugin.customobjects.MyObject;
import ie.ucd.semanticproperties.plugin.exceptions.UnknownVariableIdentifierException;
import ie.ucd.semanticproperties.plugin.structs.LevelRepresenation;
import ie.ucd.semanticproperties.plugin.structs.RegExpStruct;

public class SemanticPropertyInstance {
  
  private LevelId level;
  private ArrayList<ScopeId> scope;
  private String propId;
  private HashMap<String,Object> captured; 
  //TODO args to constructor (Map<String,?>,propId,scope,level)
  public SemanticPropertyInstance(String input,LevelRepresenation propIn) {
    /**
     * Assign scope, level and Id.
     */
    scope = propIn.getScope();
    level = propIn.getLevel();
    propId = propIn.getName();
    /**
     * Match Instance
     */
    Pattern p = Pattern.compile(propIn.getReg().getExp());
    Matcher m = p.matcher(input);
    /**
     * Fill HashMap with the captured variables for this Instance.
     */
    HashMap<String, Integer> intMap  = propIn.getReg().getGroupInt();
    HashMap<String, MyObject> obMap = propIn.getReg().getGroupObj();
    for(String s:intMap.keySet()) {
      
      MyObject ob = obMap.get(s);
      ob.setValue(m.group(intMap.get(s)));
      captured.put(s, ob.getValue());
    }
    
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

}
