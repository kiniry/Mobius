package prover.gui;

import org.eclipse.jface.text.IDocument;

import prover.gui.editor.BasicSourceViewerConfig;
import prover.gui.editor.LimitRuleScanner;
import prover.gui.editor.ProverEditor;

/**
 * A data structure to have an easy way to handle the different 
 * elements associated with a prover editor.
 * @author J. Charles
 */
public class ProverFileContext {
	/**
	 * An empty context (all its variable have a <code>null</code> value).
	 */
	public static final ProverFileContext empty = new ProverFileContext(null);
	

	public final ProverEditor ce;
	public final IDocument doc; 
	public final BasicSourceViewerConfig sv; 
	public final LimitRuleScanner scan;
	
	
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
		}
		else {
			sv = ce.getSourceViewerConfig();
			doc = sv.getPresentationReconciler().getDocument();			
			scan = sv.getTagScanner();
		}
	}
}
