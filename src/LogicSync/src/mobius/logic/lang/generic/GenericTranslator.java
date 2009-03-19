package mobius.logic.lang.generic;

import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.PrintStream;
import java.util.LinkedList;

import mobius.logic.lang.generic.ast.AEvaluator;
import mobius.logic.lang.generic.ast.Atom;
import mobius.logic.lang.generic.ast.Clause;
import mobius.logic.lang.generic.ast.GenericAst;
import mobius.logic.lang.generic.ast.Term;

public class GenericTranslator extends AEvaluator<String> {
 
  private final PrintStream fOut;
  
  public GenericTranslator(PrintStream out) {
    fOut = out;
  }
  
  public static void translate(GenericAst ast, File output) throws FileNotFoundException {
    final GenericTranslator trans = new GenericTranslator(
                                       new PrintStream(
                                          new FileOutputStream(output)));
    ast.eval(trans);
  }
  
  
  
  @Override
  public String evalApplication(final Term next, final Term first) {
    final StringBuilder res = new StringBuilder();
    Term t = first;
    while (t != null) {
      res.append(" ");
      res.append(t.eval(this));
      t = t.getNext();
    }
    return "(" + res.substring(1) + ")";
  }

  @Override
  public String evalAtom(final Term next, final String id) {
    return id;
  }

  @Override
  public String evalClauseList(final LinkedList<Clause> list) {
    final StringBuilder res = new StringBuilder();
    for (Clause c: list) {
      final String eval = c.eval(this); 
      fOut.println(eval);
      res.append(eval);
    }
    return res.toString();
  }

  @Override
  public String evalDoc(final String content) {
    return "\n[" + content + "]";
  }

  @Override
  public String evalForall(final Term next, final Atom vars, final Term term) {
    final StringBuilder strVars = new StringBuilder();
    Term var = vars;
    while (var != null) {
      strVars.append(" ");
      strVars.append(var.eval(this));
      var = var.getNext();
    }
    return "(forall" + strVars + ", " + term.eval(this) + ")";
  }

  @Override
  public String evalFormula(final String id, final Term term) {
    return id + ": " + term.eval(this);
  }

  @Override
  public String evalPredicate(final String id, final int arity) {
    return id + "(" + arity + ")";
  }

  @Override
  public String evalSymbol(final String id) {
    return id;
  }

  /** {@inheritDoc} */
  @Override
  public String evalTerm(final Term next) {
    return null;
  }

}
