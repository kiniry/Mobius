package umbra.editor;

import org.eclipse.jface.text.BadLocationException;
import org.eclipse.jface.text.DocumentEvent;
import org.eclipse.jface.text.IDocument;
import org.eclipse.ui.IActionBars;

import annot.bcclass.BCClass;
import annot.bcclass.attributes.BCPrintableAttribute;

public class BMLParsing {
  
  public boolean enabled = false;
  private BCClass bcc;
  private BCPrintableAttribute[] lines;
  private BCPrintableAttribute[] attributes;
  private IDocument doc;
  private int lc;
  private int old_lc = -1;
  private int change_number = 0;

  private void syso(String msg) {
    System.out.println(msg);
  }
  
  private void showMsg(String msg) {
    msg = "|/-\\".charAt(change_number % 4) + "  " + msg;
    final BytecodeEditor editor = ((BytecodeDocument)doc).getEditor();
    final IActionBars bars = editor.getEditorSite().getActionBars();
    bars.getStatusLineManager().setMessage(msg);
  }

  private void update_lines() {
    lines = new BCPrintableAttribute[2*lc]; //?
    if (attributes == null)
      attributes = bcc.getAllAttributes();
    for (int i=0; i<attributes.length; i++) {
      BCPrintableAttribute pa = attributes[i];
      if (pa == null) {
        syso("warning: null attribute.");
        continue;
      }
      if ((pa.line_start < 0) || (pa.line_end < 0))
        continue;
      for (int j=pa.line_start; j<pa.line_end; j++)
        lines[j] = pa;
    }
  }
  
  public BMLParsing(BCClass bcc) {
    if (!enabled)
      return;
    this.bcc = bcc;
    String code = bcc.printCode();
    old_lc = lc = code.split("\n").length+1;
    update_lines();
    syso("init");
  }

  private String getAttributeLines() {
    String ret = "";
    BCPrintableAttribute pa = null;
    for (int l=0; l<lc; l++) {
      BCPrintableAttribute curr_a = lines[l];
      if (curr_a == pa)
        continue;
      if (pa == null) {
        pa = curr_a;
        if (pa.line_start != l)
          return "error in line " + l;
      } else {
        if (pa.line_end != l)
          return "error in line " + l;
        if (ret.length() > 0)
          ret += ",  ";
        ret += "(" + pa.atype + ": " + (pa.line_start+1)
            + " -- " + (pa.line_end+1) + ")";
        pa = null;
      }
    }
    return ret;
  }

  private void replaceAttr(BCPrintableAttribute oa, BCPrintableAttribute na) {
    oa.replaceWith(na);
    for (int j=na.line_start; j<na.line_end; j++)
      lines[j] = na;
    for (int i=0; i<attributes.length; i++)
      if (attributes[i] == oa)
        attributes[i] = na;
  }
  
  public void onChange(DocumentEvent event) {
    if (!enabled)
      return;
    syso("onChange");
    change_number++;
    doc = event.fDocument;
    lc = doc.getNumberOfLines();
    try {
      int ins = event.fText.split("\n").length;
      int rem = old_lc - lc + ins;
      int pos = event.fDocument.getLineOfOffset(event.fOffset)-1;
      boolean lstart = event.fDocument.getLineOffset(pos+1) == event.fOffset;
      for (int l=pos; l<lc; l++) {
        if (lines[l] == null)
          continue;
        if (l > pos)
          if (lines[l] == lines[l-1])
            continue;
        if (lines[l].line_start > pos + (lstart ? 0 : 1))
          lines[l].line_start += ins - rem;
        lines[l].line_end += ins - rem;
      }
      update_lines();
      BCPrintableAttribute pa = lines[pos];
      if (pa != null) {
        String code = doc.get();
        code = code.substring(doc.getLineOffset(pa.line_start),
                              doc.getLineOffset(pa.line_end));
        BCPrintableAttribute na = bcc.parser.checkSyntax(pa,
          bcc.parser.removeComment(code));
        if (na == null) {
          showMsg("error");
        } else {
          replaceAttr(pa, na);
          showMsg("ok");
        }
      } else {
        showMsg(getAttributeLines()
                + ": " + pos + " +" + ins + " -" + rem + "  ");
      }
    } catch (BadLocationException e) {
      showMsg("EXCEPTION occured!");
      e.printStackTrace();
    }
    old_lc = lc;
    doc = null; //?
  }
}
