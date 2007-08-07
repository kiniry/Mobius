/*
 * @title       "BoogiePL in Umbra"
 * @description "BoobiePL support for Umbra bytecode editor"
 * @copyright   ""
 * @license     ""
 */
package umbra.editor.boogiepl;

import org.eclipse.jface.text.rules.IWhitespaceDetector;

import umbra.editor.parsing.BytecodeWhitespaceDetector;

/**
 * New definition of whitespace. This class is nothing but a delegate to
 * {@link BytecodeWhitespaceDetector BytecodeWhitespaceDetector}.
 *
 * @author Samuel Willimann (wsamuel@student.ethz.ch)
 * @version a-01
 */
public class BoogiePLWhitespaceDetector implements IWhitespaceDetector {


  /**
   * TODO.
   */
  private BytecodeWhitespaceDetector my_decorator;

  /**
   * This constructor creates a delegate to {@link BytecodeWhitespaceDetector}
   * which simply does the same job.
   */
  public BoogiePLWhitespaceDetector() {
    my_decorator = new BytecodeWhitespaceDetector();
  }

  /**
   * TODO.
   * @param a_char TODO
   * @return TODO
   */
  public final boolean isWhitespace(final char a_char) {
    return my_decorator.isWhitespace(a_char);
  }
}
