package jml2bml.plugin;

public class NotTranslatedException extends Exception {
  /**
   * 
   */
  private static final long serialVersionUID = 4915746120901185117L;

  public NotTranslatedException(final Exception exc) {
    super(exc);
  }
}
