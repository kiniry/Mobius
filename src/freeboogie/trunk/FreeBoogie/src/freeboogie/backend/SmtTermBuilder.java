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
    def("and", Sort.FORMULA, Sort.FORMULA);
    def("or", Sort.FORMULA, Sort.FORMULA);
    def("implies", new Sort[]{Sort.FORMULA, Sort.FORMULA}, Sort.FORMULA);

    def("boolNand", new Sort[]{Sort.BOOL, Sort.BOOL}, Sort.BOOL);

    def("var", String.class, Sort.VARTERM);
    def("var_int", String.class, Sort.VARINT);
    def("var_bool", String.class, Sort.VARBOOL);

    def("literal_int", BigInteger.class, Sort.INT);
    def("literal_bool", Boolean.class, Sort.BOOL);
    def("literal_formula", Boolean.class, Sort.FORMULA);

    def("forall", new Sort[]{Sort.VARTERM, Sort.FORMULA}, Sort.FORMULA);
    def("forall_int", new Sort[]{Sort.VARINT, Sort.FORMULA}, Sort.FORMULA);
    def("forall_bool", new Sort[]{Sort.VARBOOL, Sort.FORMULA}, Sort.FORMULA);
    def("exists", new Sort[]{Sort.VARTERM, Sort.FORMULA}, Sort.FORMULA);
    def("exists_int", new Sort[]{Sort.VARINT, Sort.FORMULA}, Sort.FORMULA);
    def("exists_bool", new Sort[]{Sort.VARBOOL, Sort.FORMULA}, Sort.FORMULA);

    def("+", new Sort[]{Sort.INT, Sort.INT}, Sort.INT);
    def("-", new Sort[]{Sort.INT, Sort.INT}, Sort.INT);
    def("*", new Sort[]{Sort.INT, Sort.INT}, Sort.INT);
    def("/", new Sort[]{Sort.INT, Sort.INT}, Sort.INT);
    def("%", new Sort[]{Sort.INT, Sort.INT}, Sort.INT);
    def("<", new Sort[]{Sort.INT, Sort.INT}, Sort.TERM);

    def("eq", new Sort[]{Sort.TERM, Sort.TERM}, Sort.FORMULA);
    def("eq_int", new Sort[]{Sort.INT, Sort.INT}, Sort.FORMULA);
    def("neq", new Sort[]{Sort.TERM, Sort.TERM}, Sort.FORMULA);
    def("neq_int", new Sort[]{Sort.INT, Sort.INT}, Sort.FORMULA);

    def("tuple", Sort.TERM, Sort.TERM);
    def("map_select", new Sort[]{Sort.TERM, Sort.TERM}, Sort.TERM);
    def("map_select_int", new Sort[]{Sort.TERM, Sort.TERM}, Sort.INT);
    def("map_select_bool", new Sort[]{Sort.TERM, Sort.TERM}, Sort.BOOL);
    def("map_update", new Sort[]{Sort.TERM, Sort.TERM, Sort.TERM}, Sort.TERM);
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
