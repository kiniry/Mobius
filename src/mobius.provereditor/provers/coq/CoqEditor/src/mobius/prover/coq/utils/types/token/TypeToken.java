package mobius.prover.coq.utils.types.token;

import mobius.prover.coq.utils.types.token.data.ATokenData;

import org.eclipse.jface.text.rules.IToken;


public class TypeToken implements IToken {
  
  
  private final ATokenData fData;

  public TypeToken(final ATokenData begin) {
    fData = begin;
  }
  
  /** {@inheritDoc} */
  public boolean isUndefined() {
    return false;
  }
  
  /** {@inheritDoc} */
  public boolean isWhitespace() {
    return false;
  }
  
  /** {@inheritDoc} */
  public boolean isEOF() {
    return false;
  }
  
  /** {@inheritDoc} */
  public boolean isOther() {
    return true;
  }

  /** {@inheritDoc} */
  public Object getData() {
    return fData;
  }

}
