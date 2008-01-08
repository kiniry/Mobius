package jml2bml.exceptions;

public class NotTranslatedException extends RuntimeException {
  private static final long serialVersionUID = 821440172563056853L;
  public NotTranslatedException(String msg) {
    super(msg);
  }
}
