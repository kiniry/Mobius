package umbra.editor;

import org.eclipse.jface.text.DocumentEvent;
import org.eclipse.ui.IActionBars;

import annot.attributes.SingleAssert;
import annot.bcclass.BCClass;
import annot.bcclass.BCMethod;
import annot.textio.CodeFragment;

public class BMLParsing {
  
  public static final boolean enabled = false;
  public static final boolean umbraEnabled = true;
  
  private BCClass bcc;
  private CodeFragment cf;
  private int change_number;
  private BytecodeDocument doc;

  private void syso(String msg) {
    System.out.println(msg);
  }
  
  private void showMsg(String msg) {
    msg = "|/-\\".charAt(change_number % 4) + "  " + msg;
    final BytecodeEditor editor = doc.getEditor();
    final IActionBars bars = editor.getEditorSite().getActionBars();
    bars.getStatusLineManager().setMessage(msg);
  }

  private void addSomeAnnotations() {
    if (bcc.getAllAttributes().length > 0)
      return;
    BCMethod m = bcc.getMethod(1);
    m.addAttribute(new SingleAssert(m, 0, -1));
    m.addAttribute(new SingleAssert(m, 5, -1));
    m.addAttribute(new SingleAssert(m, 5, -1));
    m.addAttribute(new SingleAssert(m, 5, -1));
  }
  
  public BMLParsing(BCClass bcc) {
    if (!enabled) {
      syso("****** BML parsing disabled. Set BMLParsing.enabled = true to enable it. ******");
      return;
    }
    this.bcc = bcc;
    addSomeAnnotations();
    String code = bcc.printCode();
    this.cf = new CodeFragment(bcc, code);
    syso("init");
  }

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

  public BCClass getBcc() {
    return bcc;
  }

}
