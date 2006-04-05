package prover.gui.editor;


import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.presentation.IPresentationReconciler;
import org.eclipse.jface.text.rules.DefaultDamagerRepairer;
import org.eclipse.jface.text.source.ISourceViewer;
import org.eclipse.jface.text.source.SourceViewerConfiguration;

public class BasicSourceViewerConfig extends SourceViewerConfiguration implements IColorConstants {
	
	private BasicRuleScanner scanner = null;
	private BasicPresentationReconciler rc = null;
	private ProverEditor editor = null;
	
	public BasicSourceViewerConfig(ProverEditor editor) {
		super();
		this.editor = editor;
	}

	public BasicRuleScanner getTagScanner() {
		if(scanner == null) {
			scanner = editor.getScanner();
		}
		return scanner;
	}
	
	public IPresentationReconciler getPresentationReconciler(ISourceViewer sv) {
		rc = new BasicPresentationReconciler(getTagScanner());
		
		DefaultDamagerRepairer dr = new DefaultDamagerRepairer(getTagScanner());
		rc.setDamager(dr, IDocument.DEFAULT_CONTENT_TYPE);
		rc.setRepairer(dr, IDocument.DEFAULT_CONTENT_TYPE);
		
		return rc;
	}
	
	public BasicPresentationReconciler getPresentationReconciler() {
		return rc;
	}

}
