package mobius.logic.lang.coq;

import mobius.logic.lang.coq.ast.AEvaluator;
import mobius.logic.lang.coq.ast.Application;
import mobius.logic.lang.coq.ast.Axiom;
import mobius.logic.lang.coq.ast.Coercion;
import mobius.logic.lang.coq.ast.Comment;
import mobius.logic.lang.coq.ast.Definition;
import mobius.logic.lang.coq.ast.Doc;
import mobius.logic.lang.coq.ast.Evaluator;
import mobius.logic.lang.coq.ast.Exists;
import mobius.logic.lang.coq.ast.Forall;
import mobius.logic.lang.coq.ast.Formula;
import mobius.logic.lang.coq.ast.Fun;
import mobius.logic.lang.coq.ast.Hint;
import mobius.logic.lang.coq.ast.HintType;
import mobius.logic.lang.coq.ast.Inductive;
import mobius.logic.lang.coq.ast.Lemma;
import mobius.logic.lang.coq.ast.OpenScope;
import mobius.logic.lang.coq.ast.ReqType;
import mobius.logic.lang.coq.ast.Require;
import mobius.logic.lang.coq.ast.Tactic;
import mobius.logic.lang.coq.ast.Term;
import mobius.logic.lang.coq.ast.Variable;
import mobius.logic.lang.coq.ast.VariableList;

public class StringEvaluator extends AEvaluator<String>{

  @Override
  public String compute(Require req, String  lib, ReqType type) {
    return type + ": " + lib;
  }
  @Override
  public String compute(OpenScope openScope, String name) {
    return "Scope: " + name;
  }
  @Override
  public String  compute(Coercion coercion, String name, String typeFrom, String typeTo) {
    return name + ": " + typeFrom + " >-> " + typeTo;
  }
  @Override
  public String  compute(Hint openScope, HintType type, String name, String lib) {
    return "Hint " + name;
  }
  
  @Override
  public String  compute(Tactic tac, String name) {
    return "Tactic: " + name;
  }    
  
  
  @Override
  public String compute(Definition definition, String name) {
    return "def " + name;
  }
  

  @Override
  public String compute(Axiom axiom, String name, Formula form) {
    return "ax " + name + " " + form.eval(this);
  }
  

  @Override
  public String compute(Inductive ind, String name) {
    return "inductive " + name;
  }
  
  @Override
  public String compute(Lemma lemma, String name) {
    return "lem " + name;
  }
  
  @Override
  public String compute(Doc doc, String name) {
    return "doc: " + name;
  }
  @Override
  public String compute(Comment comment, String name) {
    return "comment: " + name;
  }
  @Override
  public String compute(Application application, Formula next, Formula first,
                        Formula tail) {
    // TODO Auto-generated method stub
    return null;
  }
  @Override
  public String compute(Exists exists, Formula next, Variable list,
                        Formula formula) {
    // TODO Auto-generated method stub
    return null;
  }
  @Override
  public String compute(Forall forall, Formula next, VariableList list,
                        Formula formula) {
    // TODO Auto-generated method stub
    return null;
  }
  @Override
  public String compute(Formula formula, Formula next) {
    // TODO Auto-generated method stub
    return null;
  }
  @Override
  public String compute(Fun fun, Formula next, VariableList list,
                        Formula formula) {
    // TODO Auto-generated method stub
    return null;
  }
  @Override
  public String compute(Term term, Formula next, String name) {
    // TODO Auto-generated method stub
    return null;
  }
  @Override
  public String compute(Variable variable, Variable next, String name,
                        Formula type) {
    // TODO Auto-generated method stub
    return null;
  }
  @Override
  public String compute(VariableList variableList, Variable first, Variable tail) {
    // TODO Auto-generated method stub
    return null;
  }
  
  


}
