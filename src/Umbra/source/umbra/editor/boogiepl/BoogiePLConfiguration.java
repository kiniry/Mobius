package umbra.editor.boogiepl;

import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.ITextDoubleClickStrategy;
import org.eclipse.jface.text.presentation.IPresentationReconciler;
import org.eclipse.jface.text.presentation.PresentationReconciler;
import org.eclipse.jface.text.rules.DefaultDamagerRepairer;
import org.eclipse.jface.text.source.ISourceViewer;
import org.eclipse.jface.text.source.SourceViewerConfiguration;

import umbra.editor.ColorManager;
import umbra.editor.IColorValues;
import umbra.editor.NonRuleBasedDamagerRepairer;
import umbra.editor.parsing.TokenGetter;


/**
 * This class is used by BoogiePL Editor with the matter of
 * double click strategy and color versions. It has been generated
 * automatically and some changes has been made, for example
 * involving special ways of colouring and possibility of
 * changing the coloring styles ('mod' parameter).  
 */
public class BoogiePLConfiguration extends SourceViewerConfiguration {
	/**
	 * TODO
	 */
	private BoogiePLDoubleClickStrategy doubleClickStrategy;
	/**
	 * TODO
	 */
	private BoogiePLTagScanner tagScanner;
	/**
	 * TODO
	 */
	private BoogiePLScanner scanner;
	/**
	 * TODO
	 */
	private ColorManager colorManager;
	/**
	 * TODO
	 */
	private int mod;
	
	/**
	 * TODO
	 */
	public BoogiePLConfiguration(ColorManager colorManager, int mod) {
		this.colorManager = colorManager;
		this.mod = mod;
	}

	/**
	 * TODO
	 */
	public String[] getConfiguredContentTypes(ISourceViewer sourceViewer) {
		return new String[] {
			IDocument.DEFAULT_CONTENT_TYPE,
			BoogiePLPartitionScanner.HEAD,
			BoogiePLPartitionScanner.TAG };
	}
	
	/**
	 * TODO
	 */
	public ITextDoubleClickStrategy getDoubleClickStrategy(
		ISourceViewer sourceViewer,
		String contentType) {
		if (doubleClickStrategy == null)
			doubleClickStrategy = new BoogiePLDoubleClickStrategy();
		return doubleClickStrategy;
	}

	/**
	 * TODO
	 */
	protected BoogiePLScanner getBoogiePLScanner() {
		if (scanner == null) {
			scanner = new BoogiePLScanner(colorManager, mod);
			scanner.setDefaultReturnToken(
				TokenGetter.getToken(colorManager, mod, IColorValues.DEFAULT));
		}
		return scanner;
	}
	
	/**
	 * TODO
	 */
	protected BoogiePLTagScanner getBoogiePLTagScanner() {
		if (tagScanner == null) {
			tagScanner = new BoogiePLTagScanner(colorManager, mod);
			tagScanner.setDefaultReturnToken(
				TokenGetter.getToken(colorManager, mod, IColorValues.TAG));
		}
		return tagScanner;
	}

	/**
	 * TODO
	 */
	public IPresentationReconciler getPresentationReconciler(ISourceViewer sourceViewer) {
		PresentationReconciler reconciler = new PresentationReconciler();

		DefaultDamagerRepairer dr =
			new DefaultDamagerRepairer(getBoogiePLTagScanner());
		reconciler.setDamager(dr, BoogiePLPartitionScanner.TAG);
		reconciler.setRepairer(dr, BoogiePLPartitionScanner.TAG);

		dr = new DefaultDamagerRepairer(getBoogiePLScanner());
		reconciler.setDamager(dr, IDocument.DEFAULT_CONTENT_TYPE);
		reconciler.setRepairer(dr, IDocument.DEFAULT_CONTENT_TYPE);

		NonRuleBasedDamagerRepairer ndr =
			TokenGetter.getRepairer(colorManager, mod, IColorValues.HEADER);
		reconciler.setDamager(ndr, BoogiePLPartitionScanner.HEAD);
		reconciler.setRepairer(ndr, BoogiePLPartitionScanner.HEAD);
		
		NonRuleBasedDamagerRepairer ndr2 =
			TokenGetter.getRepairer(colorManager, mod, IColorValues.THROWS);
		reconciler.setDamager(ndr2, BoogiePLPartitionScanner.THROWS);
		reconciler.setRepairer(ndr2, BoogiePLPartitionScanner.THROWS);

		return reconciler;
	}
	
}