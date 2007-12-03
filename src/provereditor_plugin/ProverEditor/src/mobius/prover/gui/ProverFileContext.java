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
  
  /** a word pattern */
  private final static Pattern pat = Pattern.compile("[^a-zA-Z_0-9]");


  public final ProverEditor ce;
  public final IDocument doc; 
  public final BasicSourceViewerConfig sv; 
  public final LimitRuleScanner scan;
  public final ITextViewer viewer;
  
  /**
   * The constructor to initialize the different fields.
   * @param ce The editor giving the different context elements.
   */
  public ProverFileContext(ProverEditor ce) {
    this.ce = ce;
    if(ce == null) {
      doc = null;
      sv = null;
      scan = null;
      viewer = null;
    }
    else {
      sv = ce.getSourceViewerConfig();
      doc = sv.getPresentationReconciler().getDocument();      
      scan = sv.getTagScanner();
      viewer = sv.getPresentationReconciler().getViewer();
      
    }
  }
  
  public Point getWordPoint() {
    Point p = viewer.getSelectedRange();
    int x = getBeginning(p.x);
    int y = getEnd(p.x);
    Point word = new Point(x, y - x);
    return word;
  }
  public String getWord() {
    String res = "";
    Point p = getWordPoint();
    try {
      res = doc.get(p.x, p.y);
    } catch (BadLocationException e) {
      e.printStackTrace();
    }
    return res;
  }
  
  
  private int getEnd(int x) {
    int end = 0;
    int len = doc.getLength();
    int diff = x + 10 > len ? len - x : 10;
    
    while(end == 0) {
      try {
        String str = doc.get(x, diff);
        Matcher m = pat.matcher(str);
        if(m.find())
          end = m.end() -1;
        if(x + diff == len)
          break;
        if(end == 0)
          diff += 10;
        
      } catch (BadLocationException e) {
        diff --;
        //e.printStackTrace();
      }
      
    }  
    return x + end;

  }
  private int getBeginning(int x) {
    int end = 0;
    int diff = x - 10 < 0 ? x : 10;
    while(end == 0) {
      try {
        String str = doc.get(x - diff, diff);
        Matcher m = pat.matcher(str);
        while(m.find())
          end = m.end();
        if(x - diff == 0)
          break;
        if(end == 0)
          diff += 10;
        
      } catch (BadLocationException e) {
        diff --;
        //e.printStackTrace();
      }
      
    }  
    return (x - diff) + end;
  }

  public IFile getFile() {
    ResourcesPlugin.getWorkspace().getRoot().getProject();
    IEditorInput ei = ce.getEditorInput();
    if(ei instanceof IFileEditorInput) {
      IFileEditorInput fei = (IFileEditorInput) ei;
      return fei.getFile();
    }
    return null;
  }
}
