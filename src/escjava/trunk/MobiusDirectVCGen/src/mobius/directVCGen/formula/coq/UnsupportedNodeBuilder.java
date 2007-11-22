package mobius.directVCGen.formula.coq;

import escjava.sortedProver.EscNodeBuilder;

public abstract class UnsupportedNodeBuilder extends EscNodeBuilder  {

  @Override
  public SPred buildXor(final SPred arg1, final SPred arg2) {
    throw new UnsupportedOperationException();
  }

  @Override
  public SReal buildReal(final double f) {
    throw new UnsupportedOperationException("Translation of reals is not supported yet!");
  }


  @Override
  public SBool buildRealBoolFun(final int realPredTag, final SReal arg1, final SReal arg2) {
    throw new UnsupportedOperationException("Translation of reals is not supported yet!");
  }


  @Override
  public SReal buildRealFun(final int realFunTag, final SReal arg1, final SReal arg2) {
    throw new UnsupportedOperationException("Translation of reals is not supported yet!");
  }


  @Override
  public SReal buildRealFun(final int realFunTag, final SReal arg1) {
    throw new UnsupportedOperationException("Translation of reals is not supported yet!");
  }

 
  @Override
  public SPred buildRealPred(final int realPredTag, final SReal arg1, final SReal arg2) {
    throw new UnsupportedOperationException("Translation of reals is not supported yet!");
  }

  @Override
  public SAny buildConstantRef(final FnSymbol c) {
    throw new UnsupportedOperationException();
  }
  


  @Override
  public SInt buildIntFun(final int intFunTag, final SInt arg1) {
    throw new UnsupportedOperationException();
  }
}
