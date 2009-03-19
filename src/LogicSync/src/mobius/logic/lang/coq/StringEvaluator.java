package mobius.logic.lang.coq;

import mobius.logic.lang.coq.ast.AEvaluator;
import mobius.logic.lang.coq.ast.Constructor;
import mobius.logic.lang.coq.ast.Formula;
import mobius.logic.lang.coq.ast.HintType;
import mobius.logic.lang.coq.ast.ReqType;
import mobius.logic.lang.coq.ast.AxiomType;
import mobius.logic.lang.coq.ast.Variable;
import mobius.logic.lang.coq.ast.VariableList;
import mobius.logic.lang.coq.ast.ConstrList;
import java.util.List;

public class StringEvaluator extends AEvaluator<String>{

  @Override
  public String evalRequire(String  lib, ReqType type) {
    return type + ": " + lib;
  }
  @Override
  public String evalOpenScope(String name) {
    return "Scope: " + name;
  }
  @Override
  public String  evalCoercion(String name, String typeFrom, String typeTo) {
    return name + ": " + typeFrom + " >-> " + typeTo;
  }
  @Override
  public String  evalHint(HintType type, List<String> names, String lib) {
    return "Hint " + names;
  }
  
  @Override
  public String  evalTactic(String name, String content) {
    return "Tactic: " + name;
  }    
  
  
  @Override
  public String evalDefinition(String name, Formula type, Formula def, String proof ) {
    return "def " + name;
  }
  

  @Override
  public String evalAxiom(AxiomType type, String name, Formula form) {
    return "ax " + name + " " + form.eval(this);
  }
  

  @Override
  public String evalInductive(String name, Formula type, ConstrList list) {
    return "inductive " + name;
  }
  
  @Override
  public String evalLemma(String name, Formula formula, String proof) {
    return "lem " + name;
  }
  
  @Override
  public String evalDoc(String name) {
    return "doc: " + name;
  }
  @Override
  public String evalComment(String name) {
    return "comment: " + name;
  }
  @Override
  public String evalApplication(Formula next, Formula first, Formula tail) {
    // TODO Auto-generated method stub
    return null;
  }
  @Override
  public String evalExists(Formula next, Variable list, Formula formula) {
    // TODO Auto-generated method stub
    return null;
  }
  @Override
  public String evalForall(Formula next, VariableList list, Formula formula) {
    // TODO Auto-generated method stub
    return null;
  }
  @Override
  public String evalFormula(Formula next) {
    // TODO Auto-generated method stub
    return null;
  }
  @Override
  public String evalFun(Formula next, VariableList list, Formula formula) {
    // TODO Auto-generated method stub
    return null;
  }
  @Override
  public String evalTerm(Formula next, String name) {
    // TODO Auto-generated method stub
    return null;
  }
  @Override
  public String evalVariable(Variable next, String name, Formula type) {
    // TODO Auto-generated method stub
    return null;
  }
  @Override
  public String evalVariableList(Variable first, Variable tail) {
    // TODO Auto-generated method stub
    return null;
  }
  @Override
  public String evalConstrList(Constructor first, Constructor last) {
    // TODO Auto-generated method stub
    return null;
  }
  @Override
  public String evalConstructor(Constructor next, String name, Formula type) {
    // TODO Auto-generated method stub
    return null;
  }

  
  


}
