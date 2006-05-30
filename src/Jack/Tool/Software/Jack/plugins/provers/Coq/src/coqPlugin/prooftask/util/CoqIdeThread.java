/*
 * Created on Feb 16, 2005
 */
package coqPlugin.prooftask.util;

import jack.plugin.perspective.ICaseExplorer;

import java.io.File;
import java.io.IOException;
import java.util.HashMap;

import jpov.structure.Goal;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.resources.IWorkspace;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.Path;
import org.eclipse.jface.viewers.ISelectionChangedListener;
import org.eclipse.jface.viewers.SelectionChangedEvent;
import org.eclipse.jface.viewers.TreeViewer;
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.IPropertyListener;
import org.eclipse.ui.IWorkbenchPage;
import org.eclipse.ui.PartInitException;
import org.eclipse.ui.PlatformUI;
import org.eclipse.ui.ide.IDE;

import coqPlugin.CoqInteractive;


/**
 *
 *  @author jcharles
 */
public class CoqIdeThread implements ISelectionChangedListener, Runnable, IPropertyListener {
	private static HashMap hmInt = new HashMap();
	private static HashMap hmGoal = new HashMap();
	private static HashMap hmExplorer = new HashMap();
	
	
	Goal g;
	ICaseExplorer explorer;
	Process p;
	String[] cmdCoqIde;
	String[] cmdCoqC;
	CoqInteractive interactive;
	File file = null;

	public CoqIdeThread(CoqInteractive action, Goal g, File tmp, ICaseExplorer explorer) {		
		file = tmp;
		interactive = action;
		this.g = g;
		this.explorer = explorer;
		IWorkbenchPage wp = PlatformUI.getWorkbench().getActiveWorkbenchWindow().getActivePage();
		IWorkspace ws = ResourcesPlugin.getWorkspace();
		IFile f = ws.getRoot().getFileForLocation(new Path(file.toString()));
		hmInt.put(f.getLocation().toString(), interactive);
		hmGoal.put(f.getLocation().toString(), g);
		hmExplorer.put(f.getLocation().toString(), explorer);
		try {
			f.getParent().refreshLocal(IResource.DEPTH_ONE, null);
			IDE.setDefaultEditor(f, "coq.CoqEditor");
			IEditorPart iep = IDE.openEditor(wp, f, true);
			iep.addPropertyListener(this);
		} catch (PartInitException e) {
			e.printStackTrace();
		} catch (CoreException e) {
			e.printStackTrace();
		}
	}

	public void run(){
	}

	/* (non-Javadoc)
	 * @see org.eclipse.jface.viewers.ISelectionChangedListener#selectionChanged(org.eclipse.jface.viewers.SelectionChangedEvent)
	 */
	public void selectionChanged(SelectionChangedEvent event) {
		((TreeViewer) event.getSource()).refresh();
		try {
			explorer.save();
		} catch (IOException e) {
			e.printStackTrace();
		}
	}

	public void propertyChanged(Object source, int propId) {

	}
	
	public static CoqInteractive getInteractive(String file) {
		return (CoqInteractive) hmInt.get(file);
	}
	public static Goal getGoal(String file) {
		return (Goal)hmGoal.get(file);
	}

	public static ICaseExplorer getExplorer(String file) {
		
		return (ICaseExplorer) hmExplorer.get(file);
	}
}
