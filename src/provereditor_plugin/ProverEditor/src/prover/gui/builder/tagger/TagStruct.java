/**
 * 
 */
package prover.gui.builder.tagger;

import java.io.Serializable;

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

import prover.gui.editor.ProverEditor;

public final class TagStruct implements Serializable {
	/** */
	private static final long serialVersionUID = 1L;
	
	public final String name;
	public final int beg;
	public final int end;
	public final String filename;
	public TagStruct (String n, int b, int e, String f) {
		name = n;
		beg = b;
		end = e;
		filename = f;			
	}
	public String toString() {
		return name + " (" + beg + ", " + end + ") -> " + filename;
	}
	public void show() {
		//System.out.println("Showing "+ this);
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
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		
	}
}