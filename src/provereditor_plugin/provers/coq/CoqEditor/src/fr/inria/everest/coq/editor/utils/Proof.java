package fr.inria.everest.coq.editor.utils;

import org.eclipse.jface.text.BadLocationException;
import org.eclipse.jface.text.IDocument;

public class Proof {
  public final int fNamePos;
  public final int fBeginPos;
  public int fEndPos = 0;
  
  public Proof(int namePos, int beginPos) {
    fNamePos = namePos;
    fBeginPos = beginPos;
  }
  
  public boolean isProofName(int pos){
    return (fNamePos >= pos) && ((fBeginPos == 0) || (fBeginPos > pos));    
  }
  
  public boolean isWithinProof(int pos){
    return (fNamePos <= pos) && ((fEndPos == 0) || (fEndPos > pos));    
  }
  
  public String getProof(IDocument doc) {
    String s = null;
    try {
      s = doc.get(fNamePos, fBeginPos - fNamePos);
    } catch (BadLocationException e) {
      e.printStackTrace();
    }
    return s;
  }
  public Object getFullProof(IDocument doc) {
    String s = null;
    try {
      s = doc.get(fNamePos, fEndPos - fNamePos);
    } catch (BadLocationException e) {
      e.printStackTrace();
    }
    return s;
  }
}
