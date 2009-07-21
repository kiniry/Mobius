package freeboogie.astutil;

import genericutils.AssociativeOperator;

import freeboogie.ast.*;

/** 
  A helper class for {@code Boogie2Printer}. It (almost) tags each
  node with whether there is an "any" below, not hidden by a quantifier.
  Because of tails the notion of "below" is somewhat strange, but the
  results should be as expected for function definitions and for the
  {@code vars} of a quantifier.
 */
public class AnyFinder extends AssociativeEvaluator<Boolean> {
  private static class Or implements AssociativeOperator<Boolean> {
    @Override public Boolean zero() { return false; }
    @Override public Boolean plus(Boolean a, Boolean b) { return a || b; }
  }

  public AnyFinder() {
    super(new Or());
  }

  @Override
  public Boolean eval(
    AtomQuant atomQuant, 
    AtomQuant.QuantType quant, 
    Declaration vars, 
    Attribute attr, 
    Expr e
  ) {
    if (vars != null) vars.eval(this);
    e.eval(this);
    return memo(atomQuant, false);
  }

  @Override
  public Boolean eval(
    Function function,
    Attribute attr,
    Signature sig,
    Declaration tail
  ) {
    if (tail != null) tail.eval(this);
    return memo(function, sig.eval(this));
  }

  @Override
  public Boolean eval(
    PrimitiveType primitiveType,
    PrimitiveType.Ptype ptype,
    int bits
  ) {
    return ptype == PrimitiveType.Ptype.ANY;
  }
}
