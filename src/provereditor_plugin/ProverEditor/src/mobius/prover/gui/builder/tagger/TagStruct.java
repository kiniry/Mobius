
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
 * @author J. Charles
 */
public final class TagStruct implements Serializable {
	/** */
	private static final long serialVersionUID = 1L;
	
	/** the word being tagged */
	public final String name;
	/** the file name of the file where the tag can be found */
	public final String filename;
	/** the beginning of the tag in the file */
	public final int beg;
	/** the end of the tag in the file */
	public final int end;
	
	
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
	public TagStruct (String name, String filename, int begin, int end) {
		this.name = name;
		this.beg = begin;
		this.end = end;
		this.filename = filename;			
	}
	
	
	/**
	 * Open an editor, and highlight the tag in the file.
	 */
	public void show() {
		IWorkbenchPage wp = PlatformUI.getWorkbench().getActiveWorkbenchWindow().getActivePage();
		IWorkspace ws = ResourcesPlugin.getWorkspace();
		IFile f = ws.getRoot().getFileForLocation(new Path(filename));
		try {
			IEditorPart ep = IDE.openEditor(wp, f, true);
			if(ep instanceof ProverEditor) {
				ITextEditor te = (ITextEditor) ep;
				te.selectAndReveal(beg, end);
			}
		} catch (PartInitException e) {
			Logger.err.println("Failed to initialize an editor for the file " + filename + ".");
			e.printStackTrace();
		}
		
	}
	
	/**
	 * Show the tag in the form "name (beg, end) -> file"
	 */
	public String toString() {
		return name + " (" + beg + ", " + end + ") -> " + filename;
	}
}