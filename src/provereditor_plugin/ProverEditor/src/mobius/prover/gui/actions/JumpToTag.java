package mobius.prover.gui.actions;

import java.util.Iterator;

import mobius.prover.gui.ProverFileContext;
import mobius.prover.gui.builder.tagger.TagStruct;
import mobius.prover.gui.builder.tagger.Tagger;
import mobius.prover.gui.editor.ProverEditor;

import org.eclipse.core.resources.IFile;


/**
 * This class is used to trigger the 'tag jumping',
 * ie. highlighting a word and afterwartd jumping to its
 * next appearance in the current project.
 *
 * @author J. Charles (julien.charles@inria.fr)
 */
public class JumpToTag extends AProverAction {

  /** {@inheritDoc} */
  @Override
  public void trigger() {
    final Tagger tagger = Tagger.instance;
    final Iterator<TagStruct> iter = tagger.getTags();
    if (iter != null) {
      final ProverEditor pe = (ProverEditor) getActiveEditor();
      final ProverFileContext pfe = new ProverFileContext(pe);
      final IFile f = pfe.getFile();
      tagger.run(f);
      
      final String word = pfe.getWord();

      while (iter.hasNext()) {
        final TagStruct ts = (TagStruct) iter.next();
        if (ts.fName.equals(word)) {
          ts.show();
          return;
        }
      }
      while (iter.hasNext()) {
        final TagStruct ts = (TagStruct) iter.next();
        if (ts.fName.equals(word)) {
          ts.show();
          return;
        }
      }
    }
    return;
  }

}
