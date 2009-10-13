package escjava.plugin.actions;

import java.util.Collection;
import java.util.Iterator;
import java.util.LinkedList;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.resources.IWorkspace;
import org.eclipse.core.runtime.IAdaptable;
import org.eclipse.core.runtime.SafeRunner;
import org.eclipse.jdt.core.ICompilationUnit;
import org.eclipse.jdt.core.IJavaProject;
import org.eclipse.jdt.core.IPackageFragment;
import org.eclipse.jdt.core.IPackageFragmentRoot;
import org.eclipse.jface.util.SafeRunnable;
import org.eclipse.swt.widgets.Display;
import org.eclipse.ui.PlatformUI;

import escjava.plugin.EscjavaPlugin;

/**
 * @author David Cok
 *
 * A base class for the enable and disable RAC classes.
 */
abstract public class ESC extends EscjavaAction {
	// FIXME - this all happens in the UI thread with no progress - is that ok?
	//  the touch operation could use a monitor
	// These operations just read information from the UI
	// and resources and change the Escjava.enabled collection.
	
	/** A collection of IResource objects that need to
	 *  be recompiled.
	 */
	private Collection<IResource> touch;

	@Override
	protected boolean start(IJavaProject jp, Collection<IAdaptable> c) {
		touch = new LinkedList<IResource>();
		return true;
	}

	protected boolean doit(IAdaptable o) throws Exception {
		boolean b;
		if (o instanceof ICompilationUnit) {
			ICompilationUnit p = (ICompilationUnit)o;
			IResource resource = p.getCorrespondingResource();
			if (resource == null) return false;
			action(resource);
			
			// Need to touch the file in order to force
			// recompilation
			touch.add(resource);
			b = true;
		} 
		else if (o instanceof IFile) {
		  IFile file = (IFile) o;
			action(file);
			touch.add(file);
			b = true;
			// FIXME - should we do IFolder?
		} 
		else if (o instanceof IJavaProject) {
			b = doProject((IJavaProject)o);
		} 
		else if (o instanceof IPackageFragmentRoot) {
			b = doPackageFragmentRoot((IPackageFragmentRoot)o);
		} 
		else if (o instanceof IPackageFragment) {
			b = doPackageFragment((IPackageFragment)o);
		} 
		else if (o instanceof IWorkspace) {
			b = doWorkspace();
		} 
		else {
			b = false;
		}
		return b;
	}
	
	/**
	 * The base class has common behavior for everthing but
	 * the action to be performed on each resource; this method
	 * is overridden to do the appropriate action.
	 * 
	 * @param r  The resource to be acted upon.
	 */
	abstract protected void action(IResource r);
	
	@Override
	protected boolean end(IJavaProject jp, Collection<IAdaptable> elements) {
		final Collection<IResource> touchList = touch;
		// FIXME - is this the right thread to use
		SafeRunner.run(new SafeRunnable() {
			public void run() throws Exception {
				Iterator<IResource> i = touchList.iterator();
				while (i.hasNext()) {
					IResource r = (IResource)i.next();
					r.touch(null);
				}
			}
		});
		// Update the decorators in the UI thread
		Display.getDefault().syncExec(new java.lang.Runnable() {
      public void run() {
        PlatformUI.getWorkbench().getDecoratorManager().update(
          EscjavaPlugin.PLUGIN_ID + ".ESCDecorator");
      }
    });
		touch = null;
		// FIXME - touch needs to be set null no matter
		// what exceptions happen where in start/doit/end
		return true;
	}
}