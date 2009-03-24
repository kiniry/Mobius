package mobius.logic.lang.coq;

import java.util.LinkedList;

import mobius.logic.lang.coq.ast.CoqAst;
import mobius.logic.lang.coq.ast.Doc;
import mobius.logic.lang.generic.ast.AEvaluator;
import mobius.logic.lang.generic.ast.Atom;
import mobius.logic.lang.generic.ast.GenericAst;
import mobius.logic.lang.generic.ast.Term;

public class ExtractToCoq extends AEvaluator<CoqAst> {

  @Override
  public CoqAst evalApplication(Term next, Term first) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public CoqAst evalAtom(Term next, String id) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public CoqAst evalClauseList(LinkedList<GenericAst> list) {
    CoqAst ast = new CoqAst();
    for (GenericAst mem: list) {
      ast.add(mem.eval(this));
    }
    return ast;
  }

  @Override
  public CoqAst evalDoc(String content) {
    return Doc.mk(content);
  }

  @Override
  public CoqAst evalForall(Term next, Atom vars, Term term) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public CoqAst evalFormula(String id, Term term) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public CoqAst evalPredicate(String id, int arity) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public CoqAst evalSymbol(String id) {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public CoqAst evalTerm(Term next) {
    // TODO Auto-generated method stub
    return null;
  }

 
}
