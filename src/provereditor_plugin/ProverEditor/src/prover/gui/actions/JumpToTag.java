package prover.gui.actions;

import java.util.HashSet;
import java.util.Iterator;

import org.eclipse.core.commands.ExecutionEvent;
import org.eclipse.core.commands.ExecutionException;
import org.eclipse.core.commands.IHandler;
import org.eclipse.core.commands.IHandlerListener;
import org.eclipse.core.resources.IFile;
import org.eclipse.ui.PlatformUI;

import prover.gui.ProverFileContext;
import prover.gui.builder.tagger.TagStruct;
import prover.gui.builder.tagger.Tagger;
import prover.gui.editor.ProverEditor;

public class JumpToTag implements IHandler{
	HashSet hm = new HashSet();
	public void addHandlerListener(IHandlerListener h) {
		hm.add(hm);

	}

	public void dispose() {

	}

	public Object execute(ExecutionEvent event) throws ExecutionException {
		Tagger tagger = Tagger.instance;
		Iterator iter = tagger.getTags();
		if(iter != null) {
			ProverEditor pe = (ProverEditor)PlatformUI.getWorkbench().getActiveWorkbenchWindow().getActivePage().getActiveEditor();
			ProverFileContext pfe = new ProverFileContext(pe);
			IFile f = pfe.getFile();
			tagger.run(f);
			
			String word = pfe.getWord();

			while(iter.hasNext()) {
				TagStruct ts = (TagStruct) iter.next();
				if(ts.name.equals(word)) {
					ts.show();
					return null;
				}
			}
		}
		return null;
	}



	public boolean isEnabled() {

		return PlatformUI.getWorkbench().getActiveWorkbenchWindow().getActivePage().getActiveEditor() instanceof ProverEditor;
	}

	public boolean isHandled() {
		return true;
	}

	public void removeHandlerListener(IHandlerListener h) {
		hm.remove(h);
	}





}
