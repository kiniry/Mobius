package umbra.editor;

import org.eclipse.jface.text.DocumentEvent;
import annot.bcclass.BCClass;
import annot.textio.CodeFragment;

/**
 * This class is responsible for communication with BMLLib
 * library (except code position synchronization, that calls
 * only stateless, static methods from BMLLib). It stores only
 * official copies of BCClass, which represents BML-annotated
 * bytecode. All the JavaClass' that are used in Umbra editor
 * should be the same (==) as the one in the corresponding BCClass
 * (accessible via {@link #getBcc()}.getJc()).
 *
 * There is one BMLParsing object per one open editor.
 *
 * @author Tomasz Batkiewicz (tb209231@students.mimuw.edu.pl)
 * @version a-01
 */
public class BMLParsing {

  /**
   * This field is set to <code>true</code> when BMLLib is used
   * for parsing changes in bytecode documents.
   */
  public static final boolean BMLLIB_ENABLED = false;

  /**
   * The field is set to <code>true</code> when the original Umbra
   * mechanisms are used to parse the changes in bytecode documents.
   */
  public static final boolean UMBRA_ENABLED = true;


  /**
   * This represents BML-annotated bytecode whose code
   * (if correct) is displayed in the editor.
   */
  private BCClass my_bcc;

  /**
   * This represents BML-annotated bytecode (the same as in
   * <code>my_bcc</code> with its current (maybe incorrect)
   * string representation and its changes since last time
   * it was correct.
   */
  private CodeFragment my_cFgmt;

  /**
   * A standard constructor. Should be used just after loading
   * a JavaClass (from file and then into BCClass).
   *
   * @param a_bcc BCClass representing bytecode in editor this
   *    object is related with. Editor's initial code should
   *    be the same as (.equal()) <code>bcc.printCode()</code>
   *    returns.
   */
  public BMLParsing(final BCClass a_bcc) {
    if (!BMLLIB_ENABLED) {
      return;
    }
    this.my_bcc = a_bcc;
    final String code = a_bcc.printCode();
    this.my_cFgmt = new CodeFragment(a_bcc, code);
  }

  /**
   * This method should be called on every bytecode document's
   * change. It parses changes made in the document into
   * its BCClass (if document is correct) and displays proper
   * message (that bytecode is correct or incorrect) in the
   * status bar.
   *
   * @param an_event -DocumentEvent describing document changes
   *    currently made, eg. event parameter of
   *    <code>documentChanged()</code> in editor's listener.
   */
  public void onChange(final DocumentEvent an_event) {
    if (!BMLLIB_ENABLED)
      return;
    String msg = "";
    my_cFgmt.modify(an_event.fOffset, an_event.fLength, an_event.fText);
    msg += "annotations status: ";
    if (my_cFgmt.isCorrect()) {
      msg += "correct";
    } else {
      msg += "incorrect";
    }
    if (!my_cFgmt.isCorrect())
      if (my_cFgmt.getErrMsg() != null)
        msg += ": " + my_cFgmt.getErrMsg();
    if (!my_cFgmt.getCode().equals(an_event.fDocument.get())) {
      throw new RuntimeException("CodeFragment's code is out of date!");
    }
  }

  /**
   * @return current bytecode (ast) with BML annotations.
   *    It is an official copy that all other classes related
   *    with the same editor should reference to (to make
   *    any changes in the bytecode).
   */
  public BCClass getBcc() {
    return my_bcc;
  }

}
