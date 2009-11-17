/*
 * This file is part of the JML2 Eclipse Plug-in Project.
 *
 * Copyright (C) 2003-2008 Swiss Federal Institute of Technology Zurich
 *
 * This library is free software; you can redistribute it and/or
 * modify it under the terms of the GNU Lesser General Public
 * License as published by the Free Software Foundation; either
 * version 2.1 of the License, or (at your option) any later version.
 *
 * This library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
 * Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public
 * License along with this library; if not, write to the Free Software
 * Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA
 *
 * Paolo Bazzi, Summer 2006
 *
 */

package ch.ethz.inf.pm.jml.plugin.internal.core;

import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.runtime.ISafeRunnable;
import org.eclipse.core.runtime.SafeRunner;
import org.eclipse.ui.plugin.AbstractUIPlugin;
import org.osgi.framework.BundleContext;

import ch.ethz.inf.pm.jml.plugin.IJmlListener;
import ch.ethz.inf.pm.jml.plugin.JmlErrorElement;

/**
 * The activator class controls the plug-in life cycle
 *
 * @author Paolo Bazzi
 * @author WMD
 */
public class JmlPlugin extends AbstractUIPlugin {

	// The plug-in ID
	public static final String PLUGIN_ID = "ch.ethz.inf.pm.jml.plugin";

	// The shared instance
	private static JmlPlugin plugin;

	private List<IJmlListener> listeners;

	/**
	 * The constructor
	 */
	public JmlPlugin() {
		plugin = this;
	}

	/*
	 * (non-Javadoc)
	 * @see org.eclipse.ui.plugin.AbstractUIPlugin#start(org.osgi.framework.BundleContext)
	 */
	@Override
	public void start(BundleContext context) throws Exception {
		super.start(context);
	}

	/*
	 * (non-Javadoc)
	 * @see org.eclipse.ui.plugin.AbstractUIPlugin#stop(org.osgi.framework.BundleContext)
	 */
	@Override
	public void stop(BundleContext context) throws Exception {
		plugin = null;
		super.stop(context);
	}

	/**
	 * Returns the shared instance
	 * @return the shared instance
	 */
	public static JmlPlugin getDefault() {
		return plugin;
	}

	/******* Listener implementations ******/
	public synchronized void addListener(IJmlListener listener) {
		getListeners().add(listener);
	}

	public synchronized void removeListener(IJmlListener listener) {
		getListeners().remove(listener);
	}

	public synchronized List<IJmlListener> getListeners() {
		if (listeners == null)
			listeners= new ArrayList<IJmlListener>();
		return listeners;
	}

	public abstract class SafeRunnable implements ISafeRunnable {
		public void handleException(Throwable exception) {
		}
	}

	public synchronized void fireJmlStartedMultiple() {
		for (final IJmlListener each : getListeners() ) {
			SafeRunner.run(new SafeRunnable() {
				public void run() throws Exception {
					each.jmlStartedMultiple();
				}
			});
		}
	}

	public synchronized void fireJmlStarted(final IFile file) { // Only public for testing purposes
		for (Iterator<IJmlListener> all= getListeners().iterator(); all.hasNext();) {
			final IJmlListener each= all.next();
			SafeRunner.run(new SafeRunnable() {
				public void run() throws Exception {
					each.jmlStarted(file);
				}
			});
		}
	}

	public synchronized void fireJmlFinishedMultiple() {
		for (Iterator<IJmlListener> all= getListeners().iterator(); all.hasNext();) {
			final IJmlListener each = all.next();
			SafeRunner.run(new SafeRunnable() {
				public void run() throws Exception {
					each.jmlFinishedMultiple();
				}
			});
		}
	}

	public synchronized void fireJmlFinished(final IFile file, final List<JmlErrorElement> result) { // Only public for testing purposes
		for (Iterator<IJmlListener> all= getListeners().iterator(); all.hasNext();) {
			final IJmlListener each = all.next();
			SafeRunner.run(new SafeRunnable() {
				public void run() throws Exception {
					each.jmlFinished(file,result);
				}
			});
		}
	}

	/******* end listener implementations ******/


	//public synchronized void runChecker(List<IFile> files, IProgressMonitor monitor) throws CoreException {
	//	new JmlCheckerRunner().run(files, monitor);
		/*
		if (files.size() > 1) {
			// for(int i=0; i<files.size(); ++i)
			// System.out.println("F[" +i+"] " + files.get(i));
			IJmlListener listener = new JmlErrorMarkerCreator(files.get(0).getProject());
			addListener(listener);
			try {
				boolean status = new JmlCheckerRunner().run(files, monitor);

				if( status ) {
					this.getLog().log(new Status(IStatus.INFO, JmlPlugin.PLUGIN_ID, "Successfully checked " + files.size() + " files."));
				} else {
					this.getLog().log(new Status(IStatus.WARNING, JmlPlugin.PLUGIN_ID, "Checking " + files.size() + " files resulted in warnings/errors."));
				}
			} finally {
				removeListener(listener);
			}
		}
		*/
	//}

	/*
	public synchronized void runChecker(IFile file, IProgressMonitor monitor) throws CoreException {
		if (file != null && isSupportedFileType(file.getName())) {
			IJmlListener listener = new JmlErrorMarkerCreator(file.getProject());
			addListener(listener);

			try {
				boolean status = new JmlCheckerRunner().run(files, monitor);
				if( status ) {
					this.getLog().log(new Status(IStatus.INFO, JmlPlugin.PLUGIN_ID, "Successfully checked " + file.getName() + "."));
				} else {
					this.getLog().log(new Status(IStatus.WARNING, JmlPlugin.PLUGIN_ID, "Checking " + file.getName() + " resulted in warnings/errors."));
				}
			} finally {
				removeListener(listener);
			}
		}
	}
	 */

	//public synchronized void runCompiler(List<IFile> files, IProgressMonitor monitor) throws CoreException  {
	//	new JmlCompilerRunner().run(files, monitor);
		/*
		if (files.size() > 0) {
			IJmlListener listener = new JmlErrorMarkerCreator(files.get(0).getProject());
			addListener(listener);

			try {
				new JmlCompilerRunner().run(files, monitor);
			} finally {
				removeListener(listener);
			}
		}
		*/
	//}

	//public synchronized void runExec(List<IFile> files, IProgressMonitor monitor) throws CoreException  {
	//	new JmlExecRunner().run(files, monitor);
		/*
		if (files.size() > 0) {
			IJmlListener listener = new JmlErrorMarkerCreator(files.get(0).getProject());
			addListener(listener);

			try {
				new JmlExecRunner().run(files, monitor);
			} finally {
				removeListener(listener);
			}
		}
		*/
	//}

	private static Pattern supportedFileTypePattern =
		Pattern.compile(".*\\.java$|" +
				".*\\.jml$|" +
				".*\\.refines-java$|" +
				".*\\.refines-spec$|" +
				".*\\.refines-jml$|" +
				".*\\.spec$|" +
				".*\\.java-refined$|" +
				".*\\.spec-refined$|" +
				".*\\.jml-refined");

	public static boolean isSupportedFileType(String name) {
		Matcher m = supportedFileTypePattern.matcher(name);
		return m.matches();
	}
}
