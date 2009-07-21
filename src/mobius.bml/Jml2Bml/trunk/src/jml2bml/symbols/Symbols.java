/*
 * @title "Jml2Bml" @description "JML to BML Compiler" @copyright "(c)
 * 2008-01-06 University of Warsaw" @license "All rights reserved. This program
 * and the accompanying materials are made available under the terms of the LGPL
 * licence see LICENCE.txt file"
 */
package jml2bml.symbols;

import java.util.HashMap;
import java.util.Map;

import annot.bcclass.BCClass;

public class Symbols {
  private Symbols parentSymbols;

  private BCClass clazz;

  private Map < String, Variable > variables;

  public Symbols() {
    parentSymbols = null;
    variables = new HashMap < String, Variable >();
  }

  /**
   * Creates new instance of Symbols, with given parentSymbols.
   * @param theparentSymbols - symbol table for enclosing block / method / class
   */
  public Symbols(final Symbols theparentSymbols) {
    this.parentSymbols = theparentSymbols;
    variables = new HashMap < String, Variable >();
  }

  /**
   * returns the variable associated with given name.
   * @param variableName variable name
   * @return variable (BoundVar instance or Localvariable instance)
   */
  public Variable get(final String variableName) {
    if (variables.containsKey(variableName)) {
      return variables.get(variableName);
    }
    if (parentSymbols == null) {
      return null;
    }
    return parentSymbols.get(variableName);
  }

  /**
   * Stores given variable.
   * @param variableName name of the variable
   * @param val the variable itself
   */
  public void put(final String variableName, final Variable val) {
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

  /**
   * Sets the class for this symbols.
   * @param aclazz new class value
   */
  public void setClass(final BCClass aclazz) {
    this.clazz = aclazz;
  }
}
