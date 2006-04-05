package prover.gui;

import org.eclipse.jface.text.FindReplaceDocumentAdapter;
import org.eclipse.jface.text.IDocument;

import prover.gui.editor.BasicRuleScanner;
import prover.gui.editor.BasicSourceViewerConfig;
import prover.gui.editor.ProverEditor;

public class ProverContext {
	public static final ProverContext empty = new ProverContext(null, null, null, null);
	public ProverEditor ce;
	public IDocument doc; 
	public FindReplaceDocumentAdapter fda; 
	public BasicSourceViewerConfig sv; 
	public BasicRuleScanner scan;
	
	public ProverContext(ProverEditor ce, IDocument doc, FindReplaceDocumentAdapter fda, BasicSourceViewerConfig sv, BasicRuleScanner scan) {
		this.ce = ce;
		this.doc = doc;
		this.fda = fda;
		this.sv = sv;
		this.scan = scan;
	}
	public ProverContext(ProverEditor ce, IDocument doc, BasicSourceViewerConfig sv, BasicRuleScanner scan) {
		this.ce = ce;
		this.doc = doc;
		this.fda = null;
		this.sv = sv;
		this.scan = scan;
	}
}
