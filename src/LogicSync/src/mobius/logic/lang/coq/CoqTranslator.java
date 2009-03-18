package mobius.logic.lang.coq;

import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.PrintStream;

import mobius.logic.lang.coq.ast.AEvaluator;
import mobius.logic.lang.coq.ast.CoqAst;
import mobius.logic.lang.coq.ast.Formula;
import mobius.logic.lang.coq.ast.HintType;
import mobius.logic.lang.coq.ast.ReqType;
import mobius.logic.lang.coq.ast.Variable;
import mobius.logic.lang.coq.ast.VariableList;

public class CoqTranslator extends AEvaluator<String> {

  private final PrintStream fOutput;

  public CoqTranslator(PrintStream printStream) {
    fOutput = printStream;
  }
  
  
  @Override
  public String evalRequire(String  lib, ReqType type) {
    final String translated = 
      "Require " + type + " " + lib + ".";
    fOutput.println(translated);
    return translated;
  }
  
  
  @Override
  public String evalOpenScope(String name) {
    final String translated = 
      "Open Scope " + name + ".";
    fOutput.println(translated);
    return translated;

  }
  
  @Override
  public String evalCoercion(String name, String typeFrom, String typeTo) {
    final String translated = 
      "Coercion " + name + ": " + typeFrom + " >-> " + typeTo + ".";
    fOutput.println(translated);
    return translated;
  }
  @Override
  public String evalDoc(String content) {
    final String translated = 
      "\n\n(**" + content + "*)";
    fOutput.println(translated);
    return translated;
  }
  @Override
  public String evalComment(String content) {
    final String translated = 
      " (*" + content + "*) ";
    fOutput.println(translated);
    return translated;
  }
  
  
  
  @Override
  public String evalHint(HintType type, String names, String lib) {
    String translated = "Hint ";
    switch (type) {
      case RewriteBk:
        translated += "Rewrite -> ";
        break;
      default:
        translated += type + " ";
    }
    translated += names.trim();
    if (!lib.equals("")) {
      translated += ": " + lib.trim();
    }
    translated += ".";
    fOutput.println(translated);
    return translated;
  }
  
  
  @Override
  public String evalTactic(String name) {
    return "Tactic: " + name;
  }    
  
  
  @Override
  public String evalDefinition(String name) {
    return "def " + name;
  }
  

  @Override
  public String evalAxiom(String name, Formula f) {
    String translated = "Axiom " + name + ": " + f.eval(this) + ".";
    fOutput.println(translated);
    return translated;
  }
  

  @Override
  public String evalInductive(String name) {
    return "inductive " + name;
  }
  
  @Override
  public String evalLemma(String name) {
    return "lem " + name;
  }
  

  
  public static void translate(CoqAst ast, File output) throws FileNotFoundException {
    CoqAst node = ast;
    CoqTranslator trans = new CoqTranslator(new PrintStream(new FileOutputStream(output)));
    while (node != null) {
      node.eval(trans);
      node = node.getNext();
    }
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


  
}
