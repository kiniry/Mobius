package prover.gui.editor;

import mobius.prover.Prover;

import org.eclipse.ui.editors.text.TextEditor;
import org.eclipse.ui.views.contentoutline.IContentOutlinePage;

import prover.gui.editor.outline.BasicContentOutline;

/**
 * The editor used to edit any prover language defined file.
 * It selects the right scanner to highlight with the right color
 * and parse for the right language.
 */
public class ProverEditor extends TextEditor{
	/** the viewer associated with the editor */
	private BasicSourceViewerConfig fViewer;
	/** a rule scanner to highlight the file in the editor */
	private LimitRuleScanner fScanner = null;
	
	
	/**
	 * Create a new editor.
	 */
	public ProverEditor() {
		super();
		setSourceViewerConfiguration(fViewer = new BasicSourceViewerConfig(this));
	}
	
	/**
	 * Return the source viewer associated with the editor.
	 * @return a source viewer, not <code>null</code>.
	 */
	public BasicSourceViewerConfig getSourceViewerConfig() {
		return fViewer;
	}
	
	
	/**
	 * Returns the scanner associated with the editor.
	 * @return A scanner to highlight the file opened in the editor.
	 */
	public LimitRuleScanner getScanner() {
		if(fScanner == null) {
			Prover p = Prover.findProverFromFile(getTitle());
			if (p != null) {
				fScanner = p.getRuleScanner();
			}
			else { 
				fScanner = new LimitRuleScanner(null);
			}
		}
		return fScanner;
	}
	public Object getAdapter(Class cl) {
		if(cl == IContentOutlinePage.class) {
			IContentOutlinePage cop = new BasicContentOutline(this);
			return cop;
		}
		else {
			return super.getAdapter(cl);
		}
	}
	 protected void initializeKeyBindingScopes() {
	        setKeyBindingScopes(new String[] { //"org.eclipse.ui.textEditorScope", 
	        		 "ProverEditor.context" });
	  }

}
