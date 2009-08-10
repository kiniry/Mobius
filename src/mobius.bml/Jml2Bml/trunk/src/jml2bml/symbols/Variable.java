/*
 * @title "Jml2Bml" @description "JML to BML Compiler" @copyright "(c)
 * 2008-01-06 University of Warsaw" @license "All rights reserved. This program
 * and the accompanying materials are made available under the terms of the LGPL
 * licence see LICENCE.txt file"
 */
package jml2bml.symbols;

import annot.bcexpression.BCExpression;
import annot.bcexpression.BoundVar;
import annot.bcexpression.FieldRef;
import annot.bcexpression.LocalVariable;

public class Variable {

  private boolean isBoundVariable;

  private boolean isLocalVariable;

  private boolean isField;

  private BCExpression var;

  public Variable(final BoundVar avar) {
    this.var = avar;
    this.isBoundVariable = true;
  }

  public Variable(final LocalVariable avar) {
    this.var = avar;
    this.isLocalVariable = true;
  }

  public Variable(final FieldRef avar) {
    this.var = avar;
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
}
