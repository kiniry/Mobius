package annot.io;

/**
 * This exception occurs when an attribute cannot be read
 * correctly from BCEL's Unknown attribute. That mean,
 * BML annotations in .class file that is being read are
 * invalid or not supported by this library and this library
 * cannot continue reading following expressions or attributes
 * (because of unknown length of unsupported annotation).
 *
 * @author Tomasz Batkiewicz (tb209231@students.mimuw.edu.pl)
 * @version a-01
 */
public class ReadAttributeException extends Exception {

  /**
   * Serial ID used for serialisation.
   */
  private static final long serialVersionUID = -3561967227749458269L;

  /**
   * A standard constructor, with single string messages
   * describing error details.
   *
   * @param msg - short error description.
   */
  public ReadAttributeException(final String msg) {
    super(msg);
  }

}
