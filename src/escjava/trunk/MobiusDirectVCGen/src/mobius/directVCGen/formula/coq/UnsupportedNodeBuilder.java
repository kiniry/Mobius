package mobius.directVCGen.formula.coq;

import escjava.sortedProver.EscNodeBuilder;

/**
 * A node builder that contains all the unsupported operation
 * of the Coq node builder.
 * @author J. Charles (julien.charles@inria.fr)
 */
public abstract class UnsupportedNodeBuilder extends EscNodeBuilder  {

  /**
   * Unsupported operation.
   * @param arg1 ignored
   * @param arg2 ignored
   * @return throws an exception
   */
  @Override
  public SPred buildXor(final SPred arg1, final SPred arg2) {
    throw new UnsupportedOperationException();
  }

  /**
   * Unsupported operation.
   * @param f ignored
   * @return throws an exception
   */
  @Override
  public SReal buildReal(final double f) {
    throw new UnsupportedOperationException("Translation of reals is not supported yet!");
  }

  /**
   * Unsupported operation.
   * @param tag ignored
   * @param arg1 ignored
   * @param arg2 ignored
   * @return throws an exception
   */
  @Override
  public SBool buildRealBoolFun(final int tag, final SReal arg1, final SReal arg2) {
    throw new UnsupportedOperationException("Translation of reals is not supported yet!");
  }

  /**
   * Unsupported operation.
   * @param tag ignored
   * @param arg1 ignored
   * @param arg2 ignored
   * @return throws an exception
   */
  @Override
  public SReal buildRealFun(final int tag, final SReal arg1, final SReal arg2) {
    throw new UnsupportedOperationException("Translation of reals is not supported yet!");
  }

  /**
   * Unsupported operation.
   * @param tag ignored
   * @param arg ignored
   * @return throws an exception
   */
  @Override
  public SReal buildRealFun(final int tag, final SReal arg) {
    throw new UnsupportedOperationException("Translation of reals is not supported yet!");
  }

  /**
   * Unsupported operation.
   * @param tag ignored
   * @param arg1 ignored
   * @param arg2 ignored
   * @return throws an exception
   */
  @Override
  public SPred buildRealPred(final int tag, final SReal arg1, final SReal arg2) {
    throw new UnsupportedOperationException("Translation of reals is not supported yet!");
  }

  /**
   * Unsupported operation.
   * @param c ignored
   * @return throws an exception
   */
  @Override
  public SAny buildConstantRef(final FnSymbol c) {
    throw new UnsupportedOperationException();
  }
  

  /**
   * Unsupported operation.
   * @param tag ignored
   * @param arg ignored
   * @return throws an exception
   */
  @Override
  public SInt buildIntFun(final int tag, final SInt arg) {
    throw new UnsupportedOperationException();
  }
}
