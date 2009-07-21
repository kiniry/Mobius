/*
 * @title "Jml2Bml" @description "JML to BML Compiler" @copyright "(c)
 * 2008-01-06 University of Warsaw" @license "All rights reserved. This program
 * and the accompanying materials are made available under the terms of the LGPL
 * licence see LICENCE.txt file"
 */
package jml2bml.symbols;

import org.jmlspecs.openjml.JmlTree.JmlVariableDecl;

import annot.bcexpression.BCExpression;
import annot.bcexpression.BoundVar;
import annot.bcexpression.FieldRef;
import annot.bcexpression.LocalVariable;

import com.sun.source.tree.Tree;

public class Variable {

  private boolean isBoundVariable;

  private boolean isLocalVariable;

  private boolean isField;

  private BCExpression var;

  private Tree jmlNode;

  public Variable(final BoundVar avar, final Tree ajmlNode) {
    this.var = avar;
    this.jmlNode = ajmlNode;
    this.isBoundVariable = true;
  }

  public Variable(final LocalVariable avar, final Tree ajmlNode) {
    this.var = avar;
    this.jmlNode = ajmlNode;
    this.isLocalVariable = true;
  }

  public Variable(final FieldRef avar, final JmlVariableDecl node) {
    this.var = avar;
    this.jmlNode = node;
    this.isField = true;
  }

  public boolean isBoundVariable() {
    return isBoundVariable;
  }

  public boolean isLocalVariable() {
    return isLocalVariable;
  }

  public boolean isField() {
    return isField;
  }

  public BCExpression getVariable() {
    return var;
  }

  public Tree getJmlNode() {
    return jmlNode;
  }
}
