package mobius.logic.lang.generic;

import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.PrintStream;
import java.util.LinkedList;

import mobius.logic.lang.generic.ast.AEvaluator;
import mobius.logic.lang.generic.ast.Atom;
import mobius.logic.lang.generic.ast.GenericAst;
import mobius.logic.lang.generic.ast.Term;
import mobius.logic.lang.generic.ast.TypeCheckedAst;

public class GenericTranslator extends AEvaluator<String> {
 
  private final PrintStream fOut;
  private final TypeChecker tc;
  
  public GenericTranslator( TypeChecker tc, PrintStream out) {
    fOut = out;
    this.tc = tc;
  }
  
  public static void translate(TypeCheckedAst ast, File output) throws FileNotFoundException {
    final GenericTranslator trans = new GenericTranslator(ast.getTypeChecker(),
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
      res.append(" " + tc.getType(t));
      t = t.getNext();
    }
    return "(" + res.substring(1) + ")";
  }

  @Override
  public String evalAtom(final Term next, final String id) {
    return id;
  }

  @Override
  public String evalClauseList(final LinkedList<GenericAst> list) {
    final StringBuilder res = new StringBuilder();
    for (GenericAst c: list) {
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
      strVars.append(" " + tc.getType(var));
      var = var.getNext();
    }
    return "(forall" + strVars + ", " + term.eval(this) + ")";
  }

  @Override
  public String evalClause(final String id, final Term term) {
    return id + ": " + term.eval(this);
  }



  /** {@inheritDoc} */
  @Override
  public String evalTerm(final Term next) {
    return null;
  }

}
