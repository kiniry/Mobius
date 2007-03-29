package b2bpl.bytecode.bml.ast;


public class BMLLoopInvariant {

  private final BMLPredicate predicate;

  public BMLLoopInvariant(BMLPredicate predicate) {
    this.predicate = predicate;
  }

  public BMLPredicate getPredicate() {
    return predicate;
  }

  public String toString() {
    return "loop_invariant " + predicate + ";";
  }
}
