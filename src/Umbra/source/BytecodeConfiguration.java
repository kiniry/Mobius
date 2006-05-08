package umbra;

import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.ITextDoubleClickStrategy;
import org.eclipse.jface.text.presentation.IPresentationReconciler;
import org.eclipse.jface.text.presentation.PresentationReconciler;
import org.eclipse.jface.text.rules.DefaultDamagerRepairer;
import org.eclipse.jface.text.source.ISourceViewer;
import org.eclipse.jface.text.source.SourceViewerConfiguration;

/**
 * This class is used by Bytecode Editor with the matter of
 * double click strategy and color versions. It has been generated
 * automatically and some changes has been made, for example
 * involving special ways of colouring and possibility of
 * changing the coloring styles ('mod' parameter).  
 */

public class BytecodeConfiguration extends SourceViewerConfiguration {
	private BytecodeDoubleClickStrategy doubleClickStrategy;
	private BytecodeTagScanner tagScanner;
	private BytecodeScanner scanner;
	private ColorManager colorManager;
	private int mod;
	
	public BytecodeConfiguration(ColorManager colorManager, int mod) {
		this.colorManager = colorManager;
		this.mod = mod;
	}
	public String[] getConfiguredContentTypes(ISourceViewer sourceViewer) {
		return new String[] {
			IDocument.DEFAULT_CONTENT_TYPE,
			BytecodePartitionScanner.HEAD,
			BytecodePartitionScanner.TAG };
	}
	public ITextDoubleClickStrategy getDoubleClickStrategy(
		ISourceViewer sourceViewer,
		String contentType) {
		if (doubleClickStrategy == null)
			doubleClickStrategy = new BytecodeDoubleClickStrategy();
		return doubleClickStrategy;
	}

	protected BytecodeScanner getBytecodeScanner() {
		if (scanner == null) {
			scanner = new BytecodeScanner(colorManager, mod);
			scanner.setDefaultReturnToken(
				TokenGetter.getToken(colorManager, mod, IColorValues.DEFAULT));
		}
		return scanner;
	}
	protected BytecodeTagScanner getBytecodeTagScanner() {
		if (tagScanner == null) {
			tagScanner = new BytecodeTagScanner(colorManager, mod);
			tagScanner.setDefaultReturnToken(
				TokenGetter.getToken(colorManager, mod, IColorValues.TAG));
		}
		return tagScanner;
	}

	public IPresentationReconciler getPresentationReconciler(ISourceViewer sourceViewer) {
		PresentationReconciler reconciler = new PresentationReconciler();

		DefaultDamagerRepairer dr =
			new DefaultDamagerRepairer(getBytecodeTagScanner());
		reconciler.setDamager(dr, BytecodePartitionScanner.TAG);
		reconciler.setRepairer(dr, BytecodePartitionScanner.TAG);

		dr = new DefaultDamagerRepairer(getBytecodeScanner());
		reconciler.setDamager(dr, IDocument.DEFAULT_CONTENT_TYPE);
		reconciler.setRepairer(dr, IDocument.DEFAULT_CONTENT_TYPE);

		NonRuleBasedDamagerRepairer ndr =
			TokenGetter.getRepairer(colorManager, mod, IColorValues.HEADER);
		reconciler.setDamager(ndr, BytecodePartitionScanner.HEAD);
		reconciler.setRepairer(ndr, BytecodePartitionScanner.HEAD);
		
		NonRuleBasedDamagerRepairer ndr2 =
			TokenGetter.getRepairer(colorManager, mod, IColorValues.THROWS);
		reconciler.setDamager(ndr2, BytecodePartitionScanner.THROWS);
		reconciler.setRepairer(ndr2, BytecodePartitionScanner.THROWS);

		return reconciler;
	}
	
}