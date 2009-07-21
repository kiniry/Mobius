package jml2bml.exceptions;

public class NotTranslatedException extends Exception {
  /**
   *
   */
  private static final long serialVersionUID = -8880799492732932857L;

  public NotTranslatedException(final Exception exc) {
    super(exc);
  }
}
