package mobius.prover.gui.editor;


import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.presentation.IPresentationReconciler;
import org.eclipse.jface.text.rules.DefaultDamagerRepairer;
import org.eclipse.jface.text.source.ISourceViewer;
import org.eclipse.jface.text.source.SourceViewerConfiguration;


/**
 * A viewer to use with a prover editor.
 */
public class BasicSourceViewerConfig extends SourceViewerConfiguration implements IColorConstants {
	/** the current scanner associated with the viewer */
	private LimitRuleScanner scanner = null;
	/** the reconciler associated with the editor */
	private BasicPresentationReconciler rc = null;
	/** the editor associated with the viewer */
	private ProverEditor editor = null;
	
	/**
	 * Create a source viewer based on the specified editor.
	 * @param editor the editor to be based upon
	 */
	public BasicSourceViewerConfig(ProverEditor editor) {
		super();
		this.editor = editor;
	}

	/**
	 * Returns the scanner associated with the viewer and the editor.
	 * @return a scanner
	 */
	public LimitRuleScanner getTagScanner() {
		if(scanner == null) {
			scanner = editor.getScanner();
		}
		return scanner;
	}
	
	/**
	 * Returns the last presentation reconciler that was associated
	 * with this source viewer.
	 * @return A presentation reconciler or <code>null</code> 
	 * (if called properly <code>null</code> shall not be encountered)
	 */
	public BasicPresentationReconciler getPresentationReconciler() {
		return rc;
	}
	
	/*
	 *  (non-Javadoc)
	 * @see org.eclipse.jface.text.source.SourceViewerConfiguration#getPresentationReconciler(org.eclipse.jface.text.source.ISourceViewer)
	 */
	public IPresentationReconciler getPresentationReconciler(ISourceViewer sv) {
		if (rc == null) {
			rc = new BasicPresentationReconciler(getTagScanner());	
			DefaultDamagerRepairer dr = new DefaultDamagerRepairer(getTagScanner());
			rc.setDamager(dr, IDocument.DEFAULT_CONTENT_TYPE);
			rc.setRepairer(dr, IDocument.DEFAULT_CONTENT_TYPE);
		}
		return rc;
	}
}
