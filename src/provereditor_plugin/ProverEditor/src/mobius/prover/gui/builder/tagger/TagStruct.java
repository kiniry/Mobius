
package mobius.prover.gui.builder.tagger;

import java.io.Serializable;

import mobius.prover.gui.editor.ProverEditor;
import mobius.prover.plugins.Logger;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IWorkspace;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.Path;
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.IWorkbenchPage;
import org.eclipse.ui.PartInitException;
import org.eclipse.ui.PlatformUI;
import org.eclipse.ui.ide.IDE;
import org.eclipse.ui.texteditor.ITextEditor;



/**
 * A data structure to store the tags. It contains the
 * file name, the beginning and the end of the word 
 * and the word to find back the word in a text...
 * Indeed it is a data structure to store some tags!
 * 
 * @author J. Charles (julien.charles@inria.fr)
 */
public final class TagStruct implements Serializable {
  /** */
  private static final long serialVersionUID = 1L;
  
  /** the word being tagged. */
  public final String fName;
  /** the file name of the file where the tag can be found. */
  public final String fFilename;
  /** the beginning of the tag in the file. */
  public final int fBeg;
  /** the end of the tag in the file. */
  public final int fEnd;
  
  
  /**
   * Construct a tag. It has a name (the word of the tag)
   * the filename from where it come from, the beginning
   * of the tag in the file, the end of the tag in the
   * file
   * @param name the word being tagged
   * @param filename the name of the file where the tag has
   * been found
   * @param begin the beginning of the tag in the file
   * @param end the end of the tag in the file
   */
  public TagStruct (final String name, 
                    final String filename, 
                    final int begin, 
                    final int end) {
    fName = name;
    fBeg = begin;
    fEnd = end;
    fFilename = filename;      
  }
  
  
  /**
   * Open an editor, and highlight the tag in the file.
   */
  public void show() {
    final IWorkbenchPage wp = PlatformUI.getWorkbench().getActiveWorkbenchWindow().getActivePage();
    final IWorkspace ws = ResourcesPlugin.getWorkspace();
    final IFile f = ws.getRoot().getFileForLocation(new Path(fFilename));
    try {
      final IEditorPart ep = IDE.openEditor(wp, f, true);
      if (ep instanceof ProverEditor) {
        final ITextEditor te = (ITextEditor) ep;
        te.selectAndReveal(fBeg, fEnd);
      }
    } 
    catch (PartInitException e) {
      Logger.err.println("Failed to initialize an editor for the file " + fFilename + ".");
      e.printStackTrace();
    }
    
  }
  
  /** {@inheritDoc} */
  @Override
  public String toString() {
    return fName + " (" + fBeg + ", " + fEnd + ") -> " + fFilename;
  }
}