package b2bpl.bytecode.bml.ast;


public class BMLLoopSpecification {

  private final BMLLoopModifiesClause modifies;

  private final BMLLoopInvariant invariant;

  private final BMLLoopVariant variant;

  public BMLLoopSpecification(
      BMLLoopModifiesClause modifiesClause,
      BMLLoopInvariant invariant,
      BMLLoopVariant variantFunction) {
    this.modifies = modifiesClause;
    this.invariant = invariant;
    this.variant = variantFunction;
  }

  public BMLLoopModifiesClause getModifies() {
    return modifies;
  }

  public BMLLoopInvariant getInvariant() {
    return invariant;
  }

  public BMLLoopVariant getVariant() {
    return variant;
  }

  public String toString() {
    StringBuffer sb = new StringBuffer();

    sb.append(modifies);
    sb.append(System.getProperty("line.separator"));
    sb.append(invariant);
    sb.append(System.getProperty("line.separator"));
    sb.append(variant);

    return sb.toString();
  }
}
