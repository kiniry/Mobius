package mobius.prover.coq.utils.types.token;

import mobius.prover.coq.utils.types.token.data.ATokenData;

import org.eclipse.jface.text.rules.IToken;


public class TypeToken implements IToken {
  
  
  private final ATokenData fData;

  public TypeToken(final ATokenData begin) {
    fData = begin;
  }
  
  /** {@inheritDoc} */
  @Override
  public boolean isUndefined() {
    return false;
  }
  
  /** {@inheritDoc} */
  @Override
  public boolean isWhitespace() {
    return false;
  }
  
  /** {@inheritDoc} */
  @Override
  public boolean isEOF() {
    return false;
  }
  
  /** {@inheritDoc} */
  @Override
  public boolean isOther() {
    return true;
  }

  /** {@inheritDoc} */
  @Override
  public Object getData() {
    return fData;
  }

}
