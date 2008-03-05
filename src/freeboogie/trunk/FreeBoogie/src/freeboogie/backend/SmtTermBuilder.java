package freeboogie.backend;

import freeboogie.ast.Expr;

/**
 * Builds a term tree, which looks like an S-expression.
 *
 * TODO: Register the stuff common to SMT provers here,
 *       not in the prover.
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
    // TODO Take care of simple "and" and "or" (0 or 1 args)
    //      (after you take care of registering SMT stuff here)
    return new SmtTerm(sort, termId, a);
  }

}
