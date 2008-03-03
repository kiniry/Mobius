package freeboogie.backend;

import freeboogie.ast.Expr;

/**
 * Builds a term tree, which looks like an S-expression.
 *
 * @author rgrig 
 * @author reviewed by TODO
 */
public class SmtTermBuilder extends TermBuilder {

  @Override
  public SmtTerm of(Expr e) {
    assert false;
    return null;
    // TODO
  }

  @Override
  protected Term reallyMk(Sort sort, String termId, Object a) {
    return new SmtTerm(sort, termId, a);
  }

  @Override
  protected Term reallyMk(Sort sort, String termId, Term[] a) {
    return new SmtTerm(sort, termId, a);
  }

  @Override
  protected Term reallyMkNary(Sort sort, String termId, Term[] a) {
    return new SmtTerm(sort, termId, a);
  }

}
