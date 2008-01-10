package jml2bml.engine;

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
  
  public boolean isField(){
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
