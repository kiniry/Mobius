package fr.inria.everest.coq.editor.utils.types.token;

import org.eclipse.jface.text.rules.IToken;

import fr.inria.everest.coq.editor.utils.types.token.data.ATokenData;

public class TypeToken implements IToken {
  
  
  private ATokenData fData;

  public TypeToken(ATokenData begin) {
    fData = begin;
  }

  public boolean isUndefined() {
    return false;
  }

  public boolean isWhitespace() {
    return false;
  }

  public boolean isEOF() {
    return false;
  }

  public boolean isOther() {
    return true;
  }

  public Object getData() {
    return fData;
  }

}
