package prover.gui.editor;

import org.eclipse.jface.action.IAction;
import org.eclipse.ui.editors.text.TextEditor;
import org.eclipse.ui.texteditor.ITextEditorActionConstants;

import prover.Prover;

public class ProverEditor extends TextEditor{
	private BasicSourceViewerConfig csvc;
	private LimitRuleScanner scanner = null;
	
	public ProverEditor() {
		super();
		setSourceViewerConfiguration(csvc = new BasicSourceViewerConfig(this));
	}
	
	
	public BasicSourceViewerConfig getSourceViewerConfig() {
		return csvc;
	}
	
	public void doUndo() {
		IAction undo = getAction(ITextEditorActionConstants.UNDO);
		undo.run();
	}
	
	
	public LimitRuleScanner getScanner() {
		if(scanner == null) {
			Prover p = Prover.findProverFromFile(this.getTitle());
			if (p != null) {
				scanner = p.getRuleScanner();
			}
			else { 
				scanner = new LimitRuleScanner(null);
			}
		}
		return scanner;
	}
	
}
