package freeboogie.backend;

import java.math.BigInteger;
import java.util.logging.Logger;

import freeboogie.ast.Expr;

/**
 * Builds a term tree, which looks like an S-expression.
 *
 * @author rgrig 
 */
public class SmtTermBuilder extends TermBuilder {
  private static final Logger log = Logger.getLogger("freeboogie.backend");

  public SmtTermBuilder() {
    // Register terms that are necessary to translate Boogie expressions
    // Classes that implement Prover and use this term builder should
    // know how to communicate these to the provers they wrap, including
    // the necessary axioms.
    def("not", new Sort[]{Sort.BOOL}, Sort.BOOL);
    def("and", Sort.BOOL, Sort.BOOL);
    def("or", Sort.BOOL, Sort.BOOL);
    def("implies", new Sort[]{Sort.BOOL, Sort.BOOL}, Sort.BOOL);
    def("iff", new Sort[]{Sort.BOOL, Sort.BOOL}, Sort.BOOL);

    def("var", String.class, Sort.VARVALUE);
    def("var_int", String.class, Sort.VARINT);
    def("var_bool", String.class, Sort.VARBOOL);
    def("var_pred", String.class, Sort.BOOL);

    def("const", String.class, Sort.VALUE);
    def("const_int", String.class, Sort.INT);
    def("const_bool", String.class, Sort.BOOL);
    def("const_pred", String.class, Sort.BOOL);

    def("literal", String.class, Sort.VALUE);
    def("literal_int", BigInteger.class, Sort.INT);
    def("literal_bool", Boolean.class, Sort.BOOL);
    def("literal_pred", Boolean.class, Sort.BOOL);

    def("forall_int", new Sort[]{Sort.VARINT, Sort.BOOL}, Sort.BOOL);

    def("+", new Sort[]{Sort.INT, Sort.INT}, Sort.INT);
    def("-", new Sort[]{Sort.INT, Sort.INT}, Sort.INT);
    def("*", new Sort[]{Sort.INT, Sort.INT}, Sort.INT);
    def("/", new Sort[]{Sort.INT, Sort.INT}, Sort.INT);
    def("%", new Sort[]{Sort.INT, Sort.INT}, Sort.INT);
    def("<", new Sort[]{Sort.INT, Sort.INT}, Sort.BOOL);
    def("<=", new Sort[]{Sort.INT, Sort.INT}, Sort.BOOL);
    def(">", new Sort[]{Sort.INT, Sort.INT}, Sort.BOOL);
    def(">=", new Sort[]{Sort.INT, Sort.INT}, Sort.BOOL);

    def("eq", new Sort[]{Sort.VALUE, Sort.VALUE}, Sort.BOOL);
    def("eq_int", new Sort[]{Sort.INT, Sort.INT}, Sort.BOOL);
    def("eq_bool", new Sort[]{Sort.BOOL, Sort.BOOL}, Sort.BOOL);
    def("neq", new Sort[]{Sort.VALUE, Sort.VALUE}, Sort.BOOL);

    def("<:", new Sort[]{Sort.VALUE, Sort.VALUE}, Sort.BOOL);
    def("tuple", Sort.VALUE, Sort.VALUE);
    def("map_select", new Sort[]{Sort.VALUE, Sort.VALUE}, Sort.VALUE);
    def("map_update", new Sort[]{Sort.VALUE, Sort.VALUE, Sort.VALUE}, Sort.VALUE);
    pushDef(); // mark the end of the prover builtin definitions
    log.info("prepared SMT term builder");
  }

  @Override
  protected SmtTerm reallyMk(Sort sort, String termId, Object a) {
    return new SmtTerm(sort, termId, a);
  }

  @Override
  protected SmtTerm reallyMk(Sort sort, String termId, Term[] a) {
    return new SmtTerm(sort, termId, a);
  }

  @Override
  protected SmtTerm reallyMkNary(Sort sort, String termId, Term[] a) {
    // TODO For "and" and "or":
    //         Eliminate ocurrences of the id element in a
    //         If there is one argument left return it
    //         If there is no argument left return the id element
    return new SmtTerm(sort, termId, a);
  }

}
