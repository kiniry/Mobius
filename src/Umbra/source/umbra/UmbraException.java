package umbra;

/**
 * This is an exception used in tracing internal exceptional flows within
 * Umbra. This exception should not be handled outside Umbra.
 *
 * @author Aleksy Schubert (alx@mimuw.edu.pl)
 * @version a-01
 *
 */
public class UmbraException extends Exception {

  /**
   * The serial ID for the exception.
   */
  private static final long serialVersionUID = -8982650711998004110L;

  /**
   * The standard way to create the exception.
   */
  public UmbraException() {
  }

}
