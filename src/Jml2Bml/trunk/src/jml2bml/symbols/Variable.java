/*
 * @title       "Jml2Bml"
 * @description "JML to BML Compiler"
 * @copyright   "(c) 2008-01-06 University of Warsaw"
 * @license     "All rights reserved. This program and the accompanying
 *               materials are made available under the terms of the LGPL
 *               licence see LICENCE.txt file"
 */
package jml2bml.symbols;

import org.jmlspecs.openjml.JmlTree.JmlVariableDecl;

import annot.bcexpression.BCExpression;
import annot.bcexpression.BoundVar;
import annot.bcexpression.FieldRef;
import annot.bcexpression.LocalVariable;

import com.sun.source.tree.Tree;

public class Variable {
  private boolean isBoundVariable = false;
  private boolean isLocalVariable = false;
  private boolean isField = false;
  private BCExpression var;
  private Tree jmlNode;
  public boolean isBoundVariable() {
    return isBoundVariable;
  }
  public boolean isLocalVariable() {
    return isLocalVariable;
  }
  
  public boolean isField() {
    return isField;
  }
  
  public Variable(BoundVar var, Tree jmlNode) {
    this.var = var;
    this.jmlNode = jmlNode;
    this.isBoundVariable = true;
  }
  public Variable(LocalVariable var, Tree jmlNode) {
    this.var = var;
    this.jmlNode = jmlNode;
    this.isLocalVariable = true;
  }
  
  public Variable(FieldRef var, JmlVariableDecl node) {  
    this.var = var;
    this.jmlNode = node;
    this.isField = true;
  }
  public BCExpression getVariable() {
    return var;
  }
  public Tree getJmlNode() {
    return jmlNode;
  }
}
