package mobius.logic.lang.coq;

import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.PrintStream;

import mobius.logic.lang.coq.ast.AEvaluator;
import mobius.logic.lang.coq.ast.ConstrList;
import mobius.logic.lang.coq.ast.Constructor;
import mobius.logic.lang.coq.ast.CoqAst;
import mobius.logic.lang.coq.ast.Formula;
import mobius.logic.lang.coq.ast.HintType;
import mobius.logic.lang.coq.ast.AxiomType;
import mobius.logic.lang.coq.ast.ReqType;
import mobius.logic.lang.coq.ast.Variable;
import mobius.logic.lang.coq.ast.VariableList;
import java.util.List;


/**
 * Basic rule of implementations: All main vernaculars have side effect. 
 * 
 * @author J. Charles (julien.charles@inria.fr)
 */
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
  public String evalHint(HintType type, List<String> names, String lib) {
    String translated = "Hint ";
    switch (type) {
      case RewriteBk:
        translated += "Rewrite ->";
        break;
      default:
        translated += type ;
    }
    for(String name: names) {
      translated += " " + name;
    }
    if (!lib.equals("")) {
      translated += ": " + lib.trim();
    }
    translated += ".";
    fOutput.println(translated);
    return translated;
  }
  
  
  @Override
  public String evalTactic(String name, String content) {
    String trans = "Ltac " + name + " := " + content + ".";
    fOutput.println(trans);
    return trans;
  }    
  
  

  

  @Override
  public String evalAxiom(AxiomType t, String name, Formula f) {
    String translated = t + " " + name + ": " + f.eval(this) + ".";
    fOutput.println(translated);
    return translated;
  }
  
  
  @Override
  public String evalDefinition(String name, Formula type, Formula def, String proof) {
    String trans = "Definition " + name;
    if (type != null) {
      trans += ": " + type.eval(this);
    }
    if (def != null) {
      trans += " := " + def.eval(this);
    }
    if (proof != null) {
      trans += ".\n" + proof;
    }
    trans += ".";
    
    fOutput.println(trans);
    return trans;
  }

  @Override
  public String evalInductive(String name, Formula type, ConstrList list) {
    String res = "Inductive " + name + ": " + type.eval(this) + ":=\n" + list.eval(this) + "\n.";
    fOutput.println(res);
    return res;
  }
  
  
  @Override
  public String evalLemma(String name, Formula formula, String proof) {
    String trans = "Lemma " + name + ": " + formula.eval(this) + ".\n" + proof + ".";
    fOutput.println(trans);
    return trans;
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
    StringBuilder builder = new StringBuilder("(" + first.eval(this));
    Formula current = first.getNext();
    while(current != null) {
      builder.append(" ");
      builder.append(current.eval(this));
      current = current.getNext();
    }
    builder.append(")");
    String res = builder.toString();
    return res;
  }


  @Override
  public String evalExists(Formula next, Variable list, Formula formula) {
    String res = "(exists " + list.eval(this) + ", " + formula.eval(this) + ")";
    return res;
  }


  @Override
  public String evalForall(Formula next, VariableList list, Formula formula) {
    String res = "(forall " + list.eval(this) + ", " + formula.eval(this) + ")";
    return res;
  }


  @Override
  public String evalFormula(Formula next) {
    return null;
  }


  @Override
  public String evalFun(Formula next, VariableList list, Formula formula) {
    String res = "(fun " + list.eval(this) + " => " + formula.eval(this) + ")";
    return res;
  }


  @Override
  public String evalTerm(Formula next, String name) {
    return name;
  }


  @Override
  public String evalVariable(Variable next, String name, Formula type) {
    String translated;
    if (type != null) {
      translated = "(" + name + ": " + type.eval(this) + ")";
    }
    else {
      translated = name; 
    }
    return translated;
  }


  @Override
  public String evalVariableList(Variable first, Variable tail) {
    StringBuilder builder = new StringBuilder(first.eval(this));
    Variable current = first.getNext();
    while(current != null) {
      builder.append(" ");
      builder.append(current.eval(this));
      current = current.getNext();
    }
    String res = builder.toString();
    return res;
  }


  @Override
  public String evalConstrList(Constructor first, Constructor last) {
    StringBuilder builder = new StringBuilder(first.eval(this));
    Constructor current = first.getNext();
    while(current != null) {
      builder.append("\n");
      builder.append(current.eval(this));
      current = current.getNext();
    }
    String res = builder.toString();
    return res;
  }


  @Override
  public String evalConstructor(Constructor next, String name, Formula type) {
    String res = "| " + name + ": " + type.eval(this);
    return res;
  }


  
}
