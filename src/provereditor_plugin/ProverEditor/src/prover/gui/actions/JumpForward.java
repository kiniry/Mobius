package prover.gui.actions;

import org.eclipse.core.commands.ExecutionEvent;
import org.eclipse.core.commands.ExecutionException;
import org.eclipse.core.commands.IHandler;
import org.eclipse.core.commands.IHandlerListener;
import org.eclipse.jface.text.rules.IToken;
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.PlatformUI;

import prover.gui.ProverFileContext;
import prover.gui.TopLevelManager;
import prover.gui.editor.BasicRuleScanner;
import prover.gui.editor.ProverEditor;
import prover.plugins.AProverTranslator;

public class JumpForward implements IHandler {

	public void addHandlerListener(IHandlerListener handlerListener) {
	}

	public void dispose() {
	}

	public Object execute(ExecutionEvent event) throws ExecutionException {
		IEditorPart ep = getActiveEditor();
		if(! (ep instanceof ProverEditor)) {
			return null;
		}
		ProverFileContext pfc = new ProverFileContext((ProverEditor) ep);
		TopLevelManager tlm = TopLevelManager.getInstance();
		int oldlimit = pfc.viewer.getSelectedRange().x;
		BasicRuleScanner parser;
		if((parser = tlm.getParser()) == null) {
			tlm.reset(pfc);
		}
		if((parser = tlm.getParser()) == null) {
			return null; // second try we give up...
		}		
		parser.setRange(pfc.doc, oldlimit, pfc.doc.getLength() - oldlimit);
		IToken tok;
		do {
			tok = parser.nextToken();
		} while(tok != AProverTranslator.SENTENCE_TOKEN && (!tok.isEOF()));
		if(!tok.isEOF()) {
			int pos = parser.getTokenOffset() + parser.getTokenLength();
			pfc.viewer.setSelectedRange(pos, 0);
			pfc.viewer.revealRange(pos, 0);
		}
		return null;
	}

	public boolean isEnabled() {
		return true;
	}

	public boolean isHandled() {
		return true;
	}

	public void removeHandlerListener(IHandlerListener handlerListener) {
	}
	
	private static IEditorPart getActiveEditor() {
		return PlatformUI.getWorkbench().getActiveWorkbenchWindow().getActivePage().getActiveEditor();
	}

}
