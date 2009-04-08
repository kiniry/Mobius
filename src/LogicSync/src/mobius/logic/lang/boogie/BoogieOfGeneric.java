package mobius.logic.lang.boogie;

import java.util.LinkedList;

import freeboogie.ast.Ast;
import mobius.logic.lang.generic.ast.ACleanEvaluator;
import mobius.logic.lang.generic.ast.Atom;
import mobius.logic.lang.generic.ast.GenericAst;
import mobius.logic.lang.generic.ast.Term;

/**
 * Constructs a Boogie AST while visiting a generic one.
 * @author rgrig@
 */
public class BoogieOfGeneric extends ACleanEvaluator<Ast> {
  /** {@inheritDoc} */
  @Override
  public Ast evalApplication(final Term next, final Term first) {
    assert false : "not implemented";
    return null;
  }

  /** {@inheritDoc} */
  @Override
  public Ast evalAtom(final Term next, final String id) {
    assert false : "not implemented";
    return null;
  }

  /** {@inheritDoc} */
  @Override
  public Ast evalClauseList(final LinkedList<GenericAst> list) {
    assert false : "not implemented";
    return null;
  }

  /** {@inheritDoc} */
  @Override
  public Ast evalDoc(final String content) {
    assert false : "not implemented";
    return null;
  }

  /** {@inheritDoc} */
  @Override
  public Ast evalForall(final Term next, final Atom vars, final Term term) {
    assert false : "not implemented";
    return null;
  }

  /** {@inheritDoc} */
  @Override
  public Ast evalFormula(final String id, final Term term) {
    assert false : "not implemented";
    return null;
  }

  /** {@inheritDoc} */
  @Override
  public Ast evalSymbol(final String id) {
    assert false : "not implemented";
    return null;
  }
}
