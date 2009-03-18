package mobius.logic.lang.coq;

import mobius.logic.lang.coq.ast.Axiom;
import mobius.logic.lang.coq.ast.Coercion;
import mobius.logic.lang.coq.ast.Comment;
import mobius.logic.lang.coq.ast.Definition;
import mobius.logic.lang.coq.ast.Doc;
import mobius.logic.lang.coq.ast.Evaluator;
import mobius.logic.lang.coq.ast.Hint;
import mobius.logic.lang.coq.ast.HintType;
import mobius.logic.lang.coq.ast.Inductive;
import mobius.logic.lang.coq.ast.Lemma;
import mobius.logic.lang.coq.ast.OpenScope;
import mobius.logic.lang.coq.ast.ReqType;
import mobius.logic.lang.coq.ast.Require;
import mobius.logic.lang.coq.ast.Tactic;

public class StringEvaluator extends Evaluator<String>{

  @Override
  public String eval(Require req, String  lib, ReqType type) {
    return type + ": " + lib;
  }
  @Override
  public String eval(OpenScope openScope, String name) {
    return "Scope: " + name;
  }
  @Override
  public String eval(Coercion coercion, String name, String typeFrom, String typeTo) {
    return name + ": " + typeFrom + " >-> " + typeTo;
  }
  @Override
  public String eval(Hint openScope, HintType type, String name, String lib) {
    return "Hint " + name;
  }
  
  @Override
  public String eval(Tactic tac, String name) {
    return "Tactic: " + name;
  }    
  
  
  @Override
  public String eval(Definition definition, String name) {
    return "def " + name;
  }
  

  @Override
  public String eval(Axiom axiom, String name) {
    return "ax " + name;
  }
  

  @Override
  public String eval(Inductive ind, String name) {
    return "inductive " + name;
  }
  
  @Override
  public String eval(Lemma lemma, String name) {
    return "lem " + name;
  }
  
  @Override
  public String eval(Doc doc, String name) {
    return "doc: " + name;
  }
  @Override
  public String eval(Comment comment, String name) {
    return "comment: " + name;
  }
  
  


}
