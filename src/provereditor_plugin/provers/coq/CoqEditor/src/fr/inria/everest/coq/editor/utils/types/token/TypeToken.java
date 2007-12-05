package fr.inria.everest.coq.editor.utils.types.token;

import org.eclipse.jface.text.rules.IToken;

import fr.inria.everest.coq.editor.utils.types.token.data.ATokenData;

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
