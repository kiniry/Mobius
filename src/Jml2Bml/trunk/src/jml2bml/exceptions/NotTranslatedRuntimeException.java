package jml2bml.exceptions;

public class NotTranslatedRuntimeException extends RuntimeException {
  private static final long serialVersionUID = 821440172563056853L;
  public NotTranslatedRuntimeException(final String msg) {
    super(msg);
  }
}
