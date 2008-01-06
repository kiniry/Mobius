package jml2bml.engine;

import java.util.HashMap;
import java.util.Map;

public class Symbols {
  private Symbols parentSymbols;

  private Map<String, Variable> variables;

  public Symbols() {
    parentSymbols = null;
    variables = new HashMap<String, Variable>();
  }

  public Symbols(Symbols parentSymbols) {
    this.parentSymbols = parentSymbols;
    variables = new HashMap<String, Variable>();
  }

  public Variable get(String variableName) {
    if (variables.containsKey(variableName)) {
      return variables.get(variableName);
    }
    if (parentSymbols == null) {
      return null;
    }
    return parentSymbols.get(variableName);
  }
  public void put(String variableName, Variable val){
    variables.put(variableName, val);
  }
}
