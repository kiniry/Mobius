package freeboogie.vcgen;

import java.util.*;

import freeboogie.ast.*;
import freeboogie.backend.*;

/**
 * Sends global axioms to the prover. These include Boogie axioms
 * and axioms for uniqueness of constants.
 * @param <T> the type of terms
 */
public class AxiomSender<T extends Term<T>> extends Transformer {
  private Prover<T> prover;
  private TermBuilder<T> term;
  private Set<T> axioms = new HashSet<T>(109);
  private List<String> uniqConst = new ArrayList<String>(109);

  public void setProver(Prover<T> prover) {
    this.prover = prover;
    this.term = prover.getBuilder();
  }

  public void process(Declaration ast) throws ProverException {
    axioms.clear();
    uniqConst.clear();
    ast.eval(this);

    ArrayList<T> uc = new ArrayList<T>(uniqConst.size());
    for (String cn : uniqConst)
      uc.add(term.mk("var", "term$$" + cn));
    axioms.add(term.mk("distinct", uc));

    for (T t : axioms) prover.assume(t);
  }

  @Override
  public void see(
    Axiom axiom,
    Attribute attr,
    String name,
    Identifiers typeArgs,
    Expr expr,
    Declaration tail
  ) {
    T a = term.of(expr);
    axioms.add(a);
    a.collectAxioms(axioms);
    if (tail != null) tail.eval(this);
  }

  @Override
  public void see(
    ConstDecl constDecl, 
    Attribute attr, 
    String id,
    Type type,
    boolean uniq,
    Declaration tail
  ) {
    if (uniq) uniqConst.add(id);
    if (tail != null) tail.eval(this);
  }
}
