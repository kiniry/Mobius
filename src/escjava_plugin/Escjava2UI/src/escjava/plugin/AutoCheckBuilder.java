/*
 * This file is part of the Esc/Java plugin project.
 * Copyright 2004 David R. Cok
 * 
 * Created on Jul 30, 2004
 *
 */
package escjava.plugin;

import java.util.Collection;
import java.util.Date;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.resources.IncrementalProjectBuilder;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Status;
import org.eclipse.jdt.core.IJavaProject;
import org.eclipse.jdt.core.JavaCore;

import pluginlib.Log;
import pluginlib.Utils;

// FIXME _ what about cancellation
// FIXME - we really need to make this incremental, both cleaning and building
/**
 * This class provides the hook with eclipse to enable automatic operations
 * upon building. That is, every time the user builds the project (every time
 * the user performs a save if auto-build is enabled) the type ESCJava checker
 * is run on all the files in the project. This class implements the <em>builders</em>
 * extension point of Eclipse.
 * 
 * This class extends IncrementalProjectBuilder which is a kind of builder that only
 * works on files that have been changed.
 * 
 * @author David R. Cok
 */
public class AutoCheckBuilder extends IncrementalProjectBuilder {
		
	/* (non-Javadoc)
	 * @see org.eclipse.core.internal.events.InternalBuilder#clean(org.eclipse.core.runtime.IProgressMonitor)
	 */
	protected void clean(IProgressMonitor pm) {
		try {
			EscjavaMarker.clearMarkers(getProject());
		} catch (CoreException e) {
			String s = "Exception while cleaning " + getProject().getName();
			Log.errorlog(s,e);
			Utils.showMessageInUI(null,"ESC/Java2 Checker cleaning",s + ": " + e);
		}
	}

	/* (non-Javadoc)
	 * @see org.eclipse.core.internal.events.InternalBuilder#build(int, java.util.Map, org.eclipse.core.runtime.IProgressMonitor)
	 */
	protected IProject[] build(int kind, Map args, IProgressMonitor monitor) throws CoreException {
			
		// This method provides the main interface to the checking process.
		// When the 'builder' is invoked, this method is executed. Since we are not really
		// building the project, but instead using Eclipse builders interface to invoke the
		// type checker, we return 'null' here.

		if (Log.on) Log.log("ESC/Java2 Builder starting " + (new Date()).toString());
		try {
			EscjavaMarker.clearMarkers(getProject());
			IJavaProject javaProject = JavaCore.create(getProject());
			EscjavaAction.Check.checkProject(javaProject);
		} catch (CoreException e) {
			throw e;
		} catch (Exception e) {
			throw new CoreException(
					new Status(IStatus.ERROR, 
							       EscjavaPlugin.PLUGIN_ID,
							       IStatus.OK, // plug-in specific value
							       "Exception caught during ESC/Java2 Checking",
							       e));
		} finally {
			if (Log.on) Log.log("ESC/Java2 Builder ending " + (new Date()));
		}
		return null;
	}
	
	// We guard access to this collection using synchronized
	// modifiers, since it is likely that different threads 
	// could be involved (e.g. UI thread in adding/removing,
	// computational thread in using a current state)
	/** The set of IResource objects that are enabled for RAC compiling. */
	static private Set enabled = new HashSet();
	

	/**
	 * Adds an IResource object to the enabled list.
	 * @param s The resource to be added, if not already present.
	 */
	synchronized
	static public void add(IResource s) {
		enabled.add(s);
	}
	
	/**
	 * Removes an IResource from the set of enabled resources.
	 * @param s The resource to be removed, if present.
	 */
	synchronized
	static public void remove(IResource s) {
		enabled.remove(s);
	}
	
	/**
	 * This method runs the argument while maintaining the synchronization
	 * lock; thus we can iterate over the collection of enabled files in
	 * a thread-safe manner.
	 * 
	 * @param r
	 */
	synchronized
	static public void run(IRunnable r) {
		r.run(enabled);
	}
	
	/** An interface to use with the run() method. */
	interface IRunnable { 
		/** The run method to be implemented by the client.
		 * 
		 * @param c The collection of enabled resources.
		 */
		public void run(Collection c); 
	}
	
	/** Returns whether the given IResource is in the collection
	 * @param r The resource to test
	 * @return true if it has been added to the collection
	 */
	synchronized
	static public boolean isEnabled(IResource r) {
		return enabled.contains(r);
	}

}

