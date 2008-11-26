package freeboogie.backend;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.logging.Logger;

import freeboogie.ast.Expr;

/**
 * Builds a term tree, which looks like an S-expression.
 *
 * @author rgrig 
 */
public class SmtTermBuilder extends TermBuilder {
  private static final Term[] termArray = new Term[0];
  private static final Logger log = Logger.getLogger("freeboogie.backend");

  public SmtTermBuilder() {
    // Register terms that are necessary to translate Boogie expressions
    // Classes that implement Prover and use this term builder should
    // know how to communicate these to the provers they wrap, including
    // the necessary axioms.
    def("not", new Sort[]{Sort.FORMULA}, Sort.FORMULA);
    def("and", Sort.FORMULA, Sort.FORMULA);
    def("or", Sort.FORMULA, Sort.FORMULA);
    def("iff", new Sort[]{Sort.FORMULA, Sort.FORMULA}, Sort.FORMULA);
    def("implies", new Sort[]{Sort.FORMULA, Sort.FORMULA}, Sort.FORMULA);
    def("Tnand", new Sort[]{Sort.BOOL, Sort.BOOL}, Sort.BOOL);

    def("var", String.class, Sort.VARTERM);
    def("var_int", String.class, Sort.VARINT);
    def("var_bool", String.class, Sort.VARBOOL);
    def("var_formula", String.class, Sort.VARFORMULA);

    def("literal", String.class, Sort.TERM);
    def("literal_int", BigInteger.class, Sort.INT);
    def("literal_bool", Boolean.class, Sort.BOOL);
    def("literal_formula", Boolean.class, Sort.FORMULA);

    def("forall", new Sort[]{Sort.VARTERM, Sort.FORMULA}, Sort.FORMULA);
    def("forall_int", new Sort[]{Sort.VARINT, Sort.FORMULA}, Sort.FORMULA);
    def("forall_bool", new Sort[]{Sort.VARBOOL, Sort.FORMULA}, Sort.FORMULA);
    def("exists", new Sort[]{Sort.VARTERM, Sort.FORMULA}, Sort.FORMULA);
    def("exists_int", new Sort[]{Sort.VARINT, Sort.FORMULA}, Sort.FORMULA);
    def("exists_bool", new Sort[]{Sort.VARBOOL, Sort.FORMULA}, Sort.FORMULA);

    def("T<", new Sort[]{Sort.INT, Sort.INT}, Sort.BOOL);
    def("+", new Sort[]{Sort.INT, Sort.INT}, Sort.INT);
    def("-", new Sort[]{Sort.INT, Sort.INT}, Sort.INT);
    def("*", new Sort[]{Sort.INT, Sort.INT}, Sort.INT);
    def("/", new Sort[]{Sort.INT, Sort.INT}, Sort.INT);
    def("%", new Sort[]{Sort.INT, Sort.INT}, Sort.INT);
    def("<", new Sort[]{Sort.INT, Sort.INT}, Sort.FORMULA);
    def("<=", new Sort[]{Sort.INT, Sort.INT}, Sort.FORMULA);
    def(">=", new Sort[]{Sort.INT, Sort.INT}, Sort.FORMULA);
    def(">", new Sort[]{Sort.INT, Sort.INT}, Sort.FORMULA);

    def("Teq", new Sort[]{Sort.TERM, Sort.TERM}, Sort.BOOL);
    def("Teq_int", new Sort[]{Sort.INT, Sort.INT}, Sort.BOOL);
    def("Teq_bool", new Sort[]{Sort.BOOL, Sort.BOOL}, Sort.BOOL);
    def("eq", new Sort[]{Sort.TERM, Sort.TERM}, Sort.FORMULA);
    def("eq_int", new Sort[]{Sort.INT, Sort.INT}, Sort.FORMULA);
    def("eq_bool", new Sort[]{Sort.BOOL, Sort.BOOL}, Sort.FORMULA);
    def("neq", new Sort[]{Sort.TERM, Sort.TERM}, Sort.FORMULA);
    def("neq_int", new Sort[]{Sort.INT, Sort.INT}, Sort.FORMULA);
    def("neq_bool", new Sort[]{Sort.BOOL, Sort.BOOL}, Sort.FORMULA);

    def("tuple", Sort.TERM, Sort.TERM);
    def("map_select", new Sort[]{Sort.TERM, Sort.TERM}, Sort.TERM);
    def("map_select_int", new Sort[]{Sort.TERM, Sort.TERM}, Sort.INT);
    def("map_select_bool", new Sort[]{Sort.TERM, Sort.TERM}, Sort.BOOL);
    def("map_update", new Sort[]{Sort.TERM, Sort.TERM, Sort.TERM}, Sort.TERM);

    def("<:", new Sort[]{Sort.TERM, Sort.TERM}, Sort.BOOL);

    // handles casts, doesn't get printed; shouldn't be in Boogie
    def("cast_to_int", new Sort[]{Sort.TERM}, Sort.INT);
    def("cast_to_bool", new Sort[]{Sort.TERM}, Sort.BOOL);

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
    if (termId.equals("and") || termId.equals("or")) {
      boolean id = termId.equals("or") ? false : true;
      ArrayList<SmtTerm> children = new ArrayList<SmtTerm>(a.length);
      for (Term t : a) {
        SmtTerm c = (SmtTerm)t;
        if (!c.id.equals("literal_formula") || (Boolean)c.data != id)
          children.add(c);
      }
      if (children.size() == 1)
        return children.get(0);
      if (children.size() == 0)
        return (SmtTerm)mk("literal_formula", Boolean.valueOf(id));
      if (children.size() != a.length)
        a = children.toArray(termArray);
    }
    return new SmtTerm(sort, termId, a);
  }
}
