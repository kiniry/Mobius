package mobius.prover.gui;

import java.util.regex.Matcher;
import java.util.regex.Pattern;

import mobius.prover.gui.editor.BasicPresentationReconciler;
import mobius.prover.gui.editor.BasicSourceViewerConfig;
import mobius.prover.gui.editor.LimitRuleScanner;
import mobius.prover.gui.editor.ProverEditor;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.jface.text.BadLocationException;
import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.ITextViewer;
import org.eclipse.swt.graphics.Point;
import org.eclipse.ui.IEditorInput;
import org.eclipse.ui.IFileEditorInput;


/**
 * A data structure to have an easy way to handle the different 
 * elements associated with a prover editor.
 * 
 * @author J. Charles (julien.charles@inria.fr)
 */
public class ProverFileContext {
  /**
   * An empty context (all its variable have a <code>null</code> value).
   */
  public static final ProverFileContext empty = new ProverFileContext(null);
  
  /** a word pattern. */
  private static final Pattern pat = Pattern.compile("[^a-zA-Z_0-9]");

  /** the document corresponding to the editor. */
  private final IDocument fDoc; 
  
  /** the currently open editor from which this context is taken. */
  private final ProverEditor fCe;

  /** the source viewer of the editor. */
  private final BasicSourceViewerConfig fSv; 
  /** the highlighting scanner of the editor. */
  private final LimitRuleScanner fScan;
  /** the viewer. */
  private final ITextViewer fViewer;
  
  /**
   * The constructor to initialize the different fields.
   * @param ce The editor giving the different context elements.
   */
  public ProverFileContext(final ProverEditor ce) {
    this.fCe = ce;
    if (ce == null) {
      fDoc = null;
      fSv = null;
      fScan = null;
      fViewer = null;
    }
    else {
      fSv = ce.getSourceViewerConfig();
      fDoc = fSv.getPresentationReconciler().getDocument();      
      fScan = fSv.getTagScanner();
      fViewer = fSv.getPresentationReconciler().getViewer();
      
    }
  }
 
  /**
   * Returns the point representing the currently selected word.
   * @return the point contains the starting offset + the length of
   * the word.
   */
  public Point getWordPoint() {
    final Point p = fViewer.getSelectedRange();
    final int x = getBeginning(p.x);
    final int y = getEnd(p.x);
    final Point word = new Point(x, y - x);
    return word;
  }
  
  /**
   * Returns the currently selected word.
   * @return not <code>null</code>
   */
  public String getWord() {
    String res = "";
    final Point p = getWordPoint();
    try {
      res = fDoc.get(p.x, p.y);
    }
    catch (BadLocationException e) {
      e.printStackTrace();
    }
    return res;
  }
  
 
  /**
   * Get the end of a word. a word is defined by the patter {@link #pat}.
   * @param off the starting offset
   * @return the ending offset
   */
  private int getEnd(final int off) {
    int end = 0;
    final int len = fDoc.getLength();
    int diff = off + 10 > len ? len - off : 10;
    
    while (end == 0) {
      try {
        final String str = fDoc.get(off, diff);
        final Matcher m = pat.matcher(str);
        if (m.find()) {
          end = m.end() - 1;
        }
        if (off + diff == len) {
          break;
        }
        if (end == 0) {
          diff += 10;
        }
        
      } 
      catch (BadLocationException e) {
        diff--;
        //e.printStackTrace();
      }
      
    }  
    return off + end;

  }
  
  /**
   * Returns the beginning of the word the given offset is a part of.
   * @param off the offset of the word
   * @return the beginning pos
   */
  private int getBeginning(final int off) {
    int end = 0;
    int diff = off - 10 < 0 ? off : 10;
    while (end == 0) {
      try {
        final String str = fDoc.get(off - diff, diff);
        final Matcher m = pat.matcher(str);
        while (m.find()) {
          end = m.end();
        }
        if (off - diff == 0) {
          break;
        }
        if (end == 0) {
          diff += 10;
        }
        
      } 
      catch (BadLocationException e) {
        diff--;
        //e.printStackTrace();
      }
      
    }  
    return (off - diff) + end;
  }

  /**
   * Returns the file opened in the editor.
   * @return a valid file or <code>null</code>
   */
  public IFile getFile() {
    ResourcesPlugin.getWorkspace().getRoot().getProject();
    final IEditorInput ei = fCe.getEditorInput();
    if (ei instanceof IFileEditorInput) {
      final IFileEditorInput fei = (IFileEditorInput) ei;
      return fei.getFile();
    }
    return null;
  }
  
  /**
   * Returns the text viewer.
   * @return the viewer
   */
  public ITextViewer getViewer() {
    return fViewer;
  }
  /**
   * Returns the document.
   * @return the document
   */
  public IDocument getDocument() {
    return fDoc;
  }
  
  /**
   * Get the highlighting limit.
   * @return a pos number
   */
  public int getLimit() {
    return fScan.getLimit();
  }
  
  /**
   * Set the limit of the highlighting.
   * @param lim a valid number
   */
  public void setLimit(final int lim) {
/*    if ( lim)
    int len = fDoc.getLength() - 1;
    if (lim < len) {
      len = lim;
    }*/
    fScan.setLimit(lim);
  }
  
  /**
   * Returns the presentation reconciler.
   * @return a valid presentation reconciler
   */
  public BasicPresentationReconciler getPresentationReconciler() {
    return fSv.getPresentationReconciler();
  }
  
  /**
   * Returns the current editor associated with this context.
   * @return a valid editor
   */
  public ProverEditor getEditor() {
    return fCe;
  }
}
