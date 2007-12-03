package mobius.prover.gui.actions;

import java.util.Iterator;

import mobius.prover.gui.ProverFileContext;
import mobius.prover.gui.builder.tagger.TagStruct;
import mobius.prover.gui.builder.tagger.Tagger;

import org.eclipse.core.resources.IFile;

import prover.gui.editor.ProverEditor;

/**
 * This class is used to trigger the 'tag jumping',
 * ie. highlighting a word and afterwartd jumping to its
 * next appearance in the current project.
 * @author J. Charles
 */
public class JumpToTag extends AProverAction{

	/*
	 * (non-Javadoc)
	 * @see prover.gui.actions.AProverAction#trigger()
	 */
	public void trigger() {
		Tagger tagger = Tagger.instance;
		Iterator<TagStruct> iter = tagger.getTags();
		if(iter != null) {
			ProverEditor pe = (ProverEditor) getActiveEditor();
			ProverFileContext pfe = new ProverFileContext(pe);
			IFile f = pfe.getFile();
			tagger.run(f);
			
			String word = pfe.getWord();

			while(iter.hasNext()) {
				TagStruct ts = (TagStruct) iter.next();
				if(ts.name.equals(word)) {
					ts.show();
					return;
				}
			}
			while(iter.hasNext()) {
				TagStruct ts = (TagStruct) iter.next();
				if(ts.name.equals(word)) {
					ts.show();
					return;
				}
			}
		}
		return;
	}

}
