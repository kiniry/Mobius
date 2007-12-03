package mobius.prover.gui.editor;


import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.presentation.IPresentationReconciler;
import org.eclipse.jface.text.rules.DefaultDamagerRepairer;
import org.eclipse.jface.text.source.ISourceViewer;
import org.eclipse.jface.text.source.SourceViewerConfiguration;


/**
 * A viewer to use with a prover editor.
 *
 * @author J. Charles (julien.charles@inria.fr)
 */
public class BasicSourceViewerConfig extends SourceViewerConfiguration 
  implements IColorConstants {
  /** the current scanner associated with the viewer. */
  private LimitRuleScanner fScanner;
  /** the reconciler associated with the editor. */
  private BasicPresentationReconciler fRc;
  /** the editor associated with the viewer. */
  private ProverEditor fEditor;
  
  /**
   * Create a source viewer based on the specified editor.
   * @param editor the editor to be based upon
   */
  public BasicSourceViewerConfig(final ProverEditor editor) {
    super();
    fEditor = editor;
  }

  /**
   * Returns the scanner associated with the viewer and the editor.
   * @return a scanner
   */
  public LimitRuleScanner getTagScanner() {
    if (fScanner == null) {
      fScanner = fEditor.getScanner();
    }
    return fScanner;
  }
  
  /**
   * Returns the last presentation reconciler that was associated
   * with this source viewer.
   * @return A presentation reconciler or <code>null</code> 
   * (if called properly <code>null</code> shall not be encountered)
   */
  public BasicPresentationReconciler getPresentationReconciler() {
    return fRc;
  }
  
  
  /** {@inheritDoc} */
  @Override
  public IPresentationReconciler getPresentationReconciler(final ISourceViewer sv) {
    if (fRc == null) {
      fRc = new BasicPresentationReconciler(getTagScanner());  
      final DefaultDamagerRepairer dr = new DefaultDamagerRepairer(getTagScanner());
      fRc.setDamager(dr, IDocument.DEFAULT_CONTENT_TYPE);
      fRc.setRepairer(dr, IDocument.DEFAULT_CONTENT_TYPE);
    }
    return fRc;
  }
}
