package mobius.prover.gui;

import java.util.regex.Matcher;
import java.util.regex.Pattern;

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
 */
public class ProverFileContext {
  /**
   * An empty context (all its variable have a <code>null</code> value).
   */
  public static final ProverFileContext empty = new ProverFileContext(null);
  
  /** a word pattern. */
  private static final Pattern pat = Pattern.compile("[^a-zA-Z_0-9]");


  public final ProverEditor fCe;
  public final IDocument fDoc; 
  public final BasicSourceViewerConfig fSv; 
  public final LimitRuleScanner fScan;
  public final ITextViewer fViewer;
  
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
  
  public Point getWordPoint() {
    final Point p = fViewer.getSelectedRange();
    final int x = getBeginning(p.x);
    final int y = getEnd(p.x);
    final Point word = new Point(x, y - x);
    return word;
  }
  
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
  
  
  private int getEnd(final int x) {
    int end = 0;
    final int len = fDoc.getLength();
    int diff = x + 10 > len ? len - x : 10;
    
    while (end == 0) {
      try {
        final String str = fDoc.get(x, diff);
        final Matcher m = pat.matcher(str);
        if (m.find()) {
          end = m.end() - 1;
        }
        if (x + diff == len) {
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
    return x + end;

  }
  private int getBeginning(final int x) {
    int end = 0;
    int diff = x - 10 < 0 ? x : 10;
    while (end == 0) {
      try {
        final String str = fDoc.get(x - diff, diff);
        final Matcher m = pat.matcher(str);
        while (m.find()) {
          end = m.end();
        }
        if (x - diff == 0) {
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
    return (x - diff) + end;
  }

  public IFile getFile() {
    ResourcesPlugin.getWorkspace().getRoot().getProject();
    final IEditorInput ei = fCe.getEditorInput();
    if (ei instanceof IFileEditorInput) {
      final IFileEditorInput fei = (IFileEditorInput) ei;
      return fei.getFile();
    }
    return null;
  }
}
