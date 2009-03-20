package mobius.logic.lang.coq;

import mobius.logic.lang.coq.ast.AEvaluator;
import mobius.logic.lang.coq.ast.Constructor;
import mobius.logic.lang.coq.ast.CoqAst;
import mobius.logic.lang.coq.ast.Formula;
import mobius.logic.lang.coq.ast.HintType;
import mobius.logic.lang.coq.ast.ReqType;
import mobius.logic.lang.coq.ast.AxiomType;
import mobius.logic.lang.coq.ast.Variable;
import mobius.logic.lang.coq.ast.VariableList;
import mobius.logic.lang.coq.ast.ConstrList;
import java.util.List;

public class StringEvaluator extends AEvaluator<String> {

  /**
   * Creates a String representation out of the given Coq Ast.
   * @param ast the AST to get the representation from
   * @return a list of commands
   */
  public static String toStringList(final CoqAst ast) {
    CoqAst node = ast;
    String res = "";
    final String sep = ",\n ";
    final StringEvaluator evaluator = new StringEvaluator();
    while (node != null) {
      res += sep + node.eval(evaluator);
      node = node.getNext();
    }
    return "[" + res.substring(sep.length()) + "]";
  }
  
  /** {@inheritDoc} */
  @Override
  public String evalRequire(final String  lib, final ReqType type) {
    return type + ": " + lib;
  }
  
  /** {@inheritDoc} */
  @Override
  public String evalOpenScope(final String name) {
    return "Scope: " + name;
  }
  
  /** {@inheritDoc} */
  @Override
  public String  evalCoercion(final String name, final String typeFrom, 
                              final String typeTo) {
    return name + ": " + typeFrom + " >-> " + typeTo;
  }
  
  /** {@inheritDoc} */
  @Override
  public String  evalHint(HintType type, List<String> names, String lib) {
    return "Hint " + names;
  }
  
  /** {@inheritDoc} */
  @Override
  public String  evalTactic(String name, String content) {
    return "Tactic: " + name;
  }    
  
  /** {@inheritDoc} */
  @Override
  public String evalDefinition(String name, Formula type, Formula def, String proof ) {
    return "def " + name;
  }
  
  /** {@inheritDoc} */
  @Override
  public String evalAxiom(AxiomType type, String name, Formula form) {
    return "ax " + name + " " + form.eval(this);
  }
  
  /** {@inheritDoc} */
  @Override
  public String evalInductive(String name, Formula type, ConstrList list) {
    return "inductive " + name;
  }
  
  /** {@inheritDoc} */
  @Override
  public String evalLemma(String name, Formula formula, String proof) {
    return "lem " + name;
  }
  
  /** {@inheritDoc} */
  @Override
  public String evalDoc(String name) {
    return "doc: " + name;
  }
  
  /** {@inheritDoc} */
  @Override
  public String evalComment(String name) {
    return "comment: " + name;
  }
  
  /** {@inheritDoc} */
  @Override
  public String evalApplication(final Formula next, final Formula first) {
    // TODO Auto-generated method stub
    return null;
  }
  
  /** {@inheritDoc} */
  @Override
  public String evalExists(Formula next, Variable list, Formula formula) {
    // TODO Auto-generated method stub
    return null;
  }
  
  /** {@inheritDoc} */
  @Override
  public String evalForall(Formula next, VariableList list, Formula formula) {
    // TODO Auto-generated method stub
    return null;
  }
  
  /** {@inheritDoc} */
  @Override
  public String evalFormula(Formula next) {
    // TODO Auto-generated method stub
    return null;
  }
  
  /** {@inheritDoc} */
  @Override
  public String evalFun(Formula next, VariableList list, Formula formula) {
    // TODO Auto-generated method stub
    return null;
  }
  
  /** {@inheritDoc} */
  @Override
  public String evalTerm(Formula next, String name) {
    // TODO Auto-generated method stub
    return null;
  }
  
  /** {@inheritDoc} */
  @Override
  public String evalVariable(Variable next, String name, Formula type) {
    // TODO Auto-generated method stub
    return null;
  }
  
  /** {@inheritDoc} */
  @Override
  public String evalVariableList(Variable first, Variable tail) {
    // TODO Auto-generated method stub
    return null;
  }
  
  /** {@inheritDoc} */
  @Override
  public String evalConstrList(Constructor first, Constructor last) {
    // TODO Auto-generated method stub
    return null;
  }
  
  /** {@inheritDoc} */
  @Override
  public String evalConstructor(final Constructor next, final String name, 
                                final Formula type) {
    return null;
  }

  @Override
  public String evalBinaryTerm(final Formula next, final Formula op, final Formula left,
                               final Formula right) {
    // TODO Auto-generated method stub
    return null;
  }

}
