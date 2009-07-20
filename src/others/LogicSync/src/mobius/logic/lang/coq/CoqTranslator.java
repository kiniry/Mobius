package mobius.logic.lang.coq;

import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.PrintStream;
import java.util.List;

import mobius.logic.lang.coq.ast.ACleanEvaluator;
import mobius.logic.lang.coq.ast.AxiomType;
import mobius.logic.lang.coq.ast.ConstrList;
import mobius.logic.lang.coq.ast.Constructor;
import mobius.logic.lang.coq.ast.CoqAst;
import mobius.logic.lang.coq.ast.Formula;
import mobius.logic.lang.coq.ast.HintType;
import mobius.logic.lang.coq.ast.ReqType;
import mobius.logic.lang.coq.ast.Variable;
import mobius.logic.lang.coq.ast.VariableList;


/**
 * Basic rule of implementations: All main vernaculars have side effect. 
 * 
 * @author J. Charles (julien.charles@inria.fr)
 */
public final class CoqTranslator extends ACleanEvaluator<String> {

  /** the file to write the Coq translation to. */
  private final PrintStream fOutput;

  
  private CoqTranslator(final PrintStream printStream) {
    fOutput = printStream;
  }
  
  
  @Override
  public String evalRequire(final String  lib, final ReqType type) {
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
  public String evalTactic(String name, String name_list, String content) {
    String trans = "Ltac " + name + " " + name_list +" := " + content + ".";
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
  public String evalLemma(final String name, final Formula formula, final String proof) {
    final String trans = "Lemma " + name + ": " + formula.eval(this) + ".\n" + proof + ".";
    fOutput.println(trans);
    return trans;
  }
  

  /**
   * Translate the AST to the Coq text version, and print it to a file.
   * @param ast the ast to translate
   * @param output the file to which to write
   * @throws FileNotFoundException if the file cannot be created
   */
  public static void translate(final CoqAst ast, 
                               final File output) throws FileNotFoundException {
    CoqAst node = ast;
    final CoqTranslator trans = new CoqTranslator(new PrintStream(
                                          new FileOutputStream(output)));
    while (node != null) {
      node.eval(trans);
      node = node.getNext();
    }
  }




  @Override
  public String evalApplication(final Formula next, final Formula first) {
    final StringBuilder builder = new StringBuilder("(" + first.eval(this));
    Formula current = first.getNext();
    while (current != null) {
      builder.append(" ");
      builder.append(current.eval(this));
      current = current.getNext();
    }
    builder.append(")");
    final String res = builder.toString();
    return res;
  }
  
  @Override
  public String evalBinaryTerm(final Formula next, final Formula op, final Formula left,
                               final Formula right) {
    
    final StringBuilder blder = new StringBuilder("(");
    blder.append(left.eval(this));
    blder.append(" ");
    blder.append(op.eval(this));
    blder.append(" ");
    blder.append(right.eval(this));
    blder.append(")");
    return blder.toString();
  }



  @Override
  public String evalExists(Formula next, Variable list, Formula formula) {
    final String res = "(exists " + list.getName() + ", " + formula.eval(this) + ")";
    return res;
  }


  @Override
  public String evalForall(Formula next, VariableList list, Formula formula) {
    final String res = "(forall " + list.eval(this) + ", " + formula.eval(this) + ")";
    return res;
  }



  @Override
  public String evalFun(final Formula next, final VariableList list, 
                        final Formula formula) {
    final String res = "(fun " + list.eval(this) + " => " + formula.eval(this) + ")";
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
    final StringBuilder builder = new StringBuilder(first.eval(this));
    Variable current = first.getNext();
    while (current != null) {
      builder.append(" ");
      builder.append(current.eval(this));
      current = current.getNext();
    }
    final String res = builder.toString();
    return res;
  }


  @Override
  public String evalConstrList(final Constructor first, 
                               final Constructor last) {
    final StringBuilder builder = new StringBuilder(first.eval(this));
    Constructor current = first.getNext();
    while (current != null) {
      builder.append("\n");
      builder.append(current.eval(this));
      current = current.getNext();
    }
    final String res = builder.toString();
    return res;
  }


  @Override
  public String evalConstructor(final Constructor next, final String name, 
                                final Formula type) {
    final String res = "| " + name + ": " + type.eval(this);
    return res;
  }




  
}
