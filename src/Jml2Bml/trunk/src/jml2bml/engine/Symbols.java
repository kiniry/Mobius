package jml2bml.engine;

import java.util.HashMap;
import java.util.Map;

import annot.bcclass.BCClass;

public class Symbols {
  private Symbols parentSymbols;

  private BCClass clazz;

  private Map<String, Variable> variables;

  public Symbols() {
    parentSymbols = null;
    variables = new HashMap<String, Variable>();
  }

  /**
   * Creates new instance of Symbols, with given parentSymbols.
   * @param parentSymbols - symbol table for enclosing block / method / class
   */
  public Symbols(final Symbols parentSymbols) {
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

  public void put(String variableName, Variable val) {
    variables.put(variableName, val);
  }

  /**
   * Finds the current BCClass.
   * @return current BCClass
   */
  public BCClass findClass() {
    if (clazz != null) {
      return clazz;
    }
    if (parentSymbols != null) {
      return parentSymbols.findClass();
    }
    return null;
  }

  public void setClass(BCClass clazz) {
    this.clazz = clazz;
    
  }
}
