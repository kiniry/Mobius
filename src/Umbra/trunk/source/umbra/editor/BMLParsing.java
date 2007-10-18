package umbra.editor;

import org.eclipse.jface.text.DocumentEvent;
import org.eclipse.ui.IActionBars;

import annot.attributes.SingleAssert;
import annot.bcclass.BCClass;
import annot.bcclass.BCMethod;
import annot.textio.CodeFragment;

/**
 * This class is responsible for communication with bmllib
 * library (except code position synchronization, that calls
 * only stateless, static methods from bmllib). It stores only
 * official copies of BCClass, which represents BML-annotated
 * bytecode. All used JavaClass'es should be the same (==)
 * as the one in it's BCClass (accessible via
 * {@link #getBcc()}.getJc()).
 * One BMLParsing per one open editor.
 * 
 * @author tomekb
 */
public class BMLParsing {
  
  /**
   * enables / disables using bmllib for parsing any changes
   * in document.
   */
  public static final boolean enabled = true;

  /**
   * enables / disables using original <code>Umbra</code>
   * mechanisms for parsing any changes in document.
   */
  public static final boolean umbraEnabled = false;
  
  //for debugging only:
  private static int last_instance_id = 0;
  private static int instance_id;
  
  /**
   * This represents BML-annotated bytecode whose code
   * (if correct) is displayed in the editor.
   */
  private BCClass bcc;
  
  /**
   * This represents BML-annotated bytecode (the same as in
   * <code>bcc</code> with it's current (may be incorrect)
   * String representation and it's changes since last time
   * it was correct.
   */
  private CodeFragment cf;
  
  /**
   * Number of edit actions, since last refresh action.
   * Used only for debug purposes.
   */
  private int change_number; //unused
  
  /**
   * currently modyfying document (the one which currently
   * handling onChange event came from).
   */
  private BytecodeDocument doc;

  /**
   * Displays a debug message (to stdout).
   * 
   * @param msg - message to be displayed.
   */
  private void syso(String msg) {
    System.out.println("(" + instance_id + ") " + msg);
  }
  
  /**
   * Changes status value to givan String. This value
   * is displayed in the status bar, at the bottom of Eclipse.
   * 
   * @param msg - new status value.
   */
  private void showMsg(String msg) {
    msg = "(" + instance_id + "): " + msg;
    msg = "|/-\\".charAt(change_number % 4) + "  " + msg;
    final BytecodeEditor editor = doc.getEditor();
    final IActionBars bars = editor.getEditorSite().getActionBars();
    bars.getStatusLineManager().setMessage(msg);
  }

  /**
   * Adds some example BML annotation to Empty.class's
   * bytecode (affecting <code>bcc</code>), if there are
   * no such annotations yet. Used only for debugging. Should
   * be removed in final version.
   */
  @SuppressWarnings("unused")
  @Deprecated
  private void addSomeAnnotations() {
    if (bcc.getAllAttributes().length > 0)
      return;
    BCMethod m = bcc.getMethod(1);
    m.addAttribute(new SingleAssert(m, 0, -1));
    m.addAttribute(new SingleAssert(m, 5, -1));
    m.addAttribute(new SingleAssert(m, 5, -1));
    m.addAttribute(new SingleAssert(m, 5, -1));
  }
  
  /**
   * A standard constructor. Should be used just after loading
   * JavaClass (from file and then into BCClass).
   * 
   * @param bcc - BCClass representing bytecode in editor this
   *    object is related with. Editor's initial code should
   *    be the same as (.equal()) <code>bcc.printCode()</code>
   *    returns.
   */
  public BMLParsing(BCClass bcc) {
    if (!enabled) {
      syso("****** BML parsing disabled. Set BMLParsing.enabled = true to enable it. ******");
      return;
    }
    this.instance_id = last_instance_id++;
    this.bcc = bcc;
//    addSomeAnnotations();
    String code = bcc.printCode();
    this.cf = new CodeFragment(bcc, code);
    syso("init");
  }

  /**
   * This method should be called on every bytecode document's
   * change. It parses changes made in the document into
   * it's BCClass (if document is correct) and displays proper
   * message (that bytecode is correct or incorrect) in the
   * status bar.
   * 
   * @param event - DocumentEvent describing document changes
   *    currently made, eg. event parameter of
   *    <code>documentChanged()</code> in editor's listener.
   */
  public void onChange(DocumentEvent event) {
    if (!enabled)
      return;
    doc = (BytecodeDocument)event.fDocument;
    change_number++;
    syso("onChange");
    String msg = "";
    cf.modify(event.fOffset, event.fLength, event.fText);
    msg += "annotations status: ";
    if (cf.isCorrect()) {
      msg += "correct";
    } else {
      msg += "incorrect";
    }
    if (!cf.isCorrect())
      if (cf.getErrMsg() != null)
        msg += ": " + cf.getErrMsg();
    syso(cf.toString());
    showMsg(msg);
    if (!cf.getCode().equals(event.fDocument.get())) {
      syso("cf.getCode="+cf.getCode());
      syso("\ndocument text="+event.fDocument.get());
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
    return bcc;
  }

}
