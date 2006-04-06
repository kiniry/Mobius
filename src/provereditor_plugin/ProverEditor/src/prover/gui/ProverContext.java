package prover.gui;

import org.eclipse.jface.text.IDocument;

import prover.gui.editor.BasicSourceViewerConfig;
import prover.gui.editor.LimitRuleScanner;
import prover.gui.editor.ProverEditor;

public class ProverContext {
	public static final ProverContext empty = new ProverContext(null, null, null, null);
	public ProverEditor ce;
	public IDocument doc; 
	public BasicSourceViewerConfig sv; 
	public LimitRuleScanner scan;
	
	public ProverContext(ProverEditor ce, IDocument doc, BasicSourceViewerConfig sv, LimitRuleScanner scan) {
		this.ce = ce;
		this.doc = doc;
		this.sv = sv;
		this.scan = scan;
	}
}
