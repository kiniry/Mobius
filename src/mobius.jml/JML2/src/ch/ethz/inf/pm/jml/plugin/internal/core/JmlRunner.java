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

import java.io.ByteArrayOutputStream;
import java.io.IOException;
import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IPath;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Status;
import org.eclipse.jdt.core.ICompilationUnit;
import org.eclipse.jdt.core.IJavaElement;
import org.eclipse.jdt.core.IJavaProject;
import org.eclipse.jdt.core.IPackageFragment;
import org.eclipse.jdt.core.IPackageFragmentRoot;
import org.eclipse.jdt.core.JavaCore;
import org.jmlspecs.checker.JmlCommonOptions;

import ch.ethz.inf.pm.jml.plugin.IJmlListener;
import ch.ethz.inf.pm.jml.plugin.JmlErrorElement;
import ch.ethz.inf.pm.jml.plugin.internal.core.properties.JmlPluginProperties;
import ch.ethz.inf.pm.jml.plugin.internal.core.properties.JmlPropertiesProvider;
import ch.ethz.inf.pm.jml.plugin.internal.ui.errors.JmlErrorMarkerCreator;
import ch.ethz.inf.pm.jml.plugin.resources.ResourceConstants;
import ch.ethz.inf.pm.jml.plugin.resources.ResourceProvider;

/**
 * @author Paolo Bazzi
 * @author WMD
 */
public abstract class JmlRunner {

	private boolean run(IFile file, IProgressMonitor monitor) {
		if( !JmlPlugin.isSupportedFileType(file.getName())) {
			// returning true should just ignore the file
			return true;
		}

		JmlPlugin.getDefault().fireJmlStarted(file);

		List<JmlErrorElement> errors = null;
		boolean result = false;
		try {
			JmlCommonOptions jmlo = null;
			try {
				jmlo = createOptions(file);
			} catch (Throwable e) {
				JmlPlugin.getDefault().getLog().log(
                        new Status(IStatus.ERROR, JmlPlugin.PLUGIN_ID, e.toString(), e));
				return false;
			}

			ByteArrayOutputStream baos = new ByteArrayOutputStream();
	        String[] arg = new String[] { file.getLocation().toOSString() };

			try {
				result = exec(arg, jmlo, baos);
			} catch (Throwable e) {
				// org.jmlspecs.checker.Main.bugReportRequest(e,arg);
				JmlPlugin.getDefault().getLog().log(
				        new Status(IStatus.ERROR, JmlPlugin.PLUGIN_ID, e.toString(), e));
			}
			errors = new ArrayList<JmlErrorElement>();
			boolean parseResult = parseOutput(baos, file, errors);
			result = result && parseResult;
			try {
				baos.close();
			} catch (IOException e) {
				JmlPlugin.getDefault().getLog().log(
				        new Status(IStatus.ERROR, JmlPlugin.PLUGIN_ID, e.getMessage(), e));
			}

			if( monitor!=null )
				monitor.worked(1);
		} finally {
			JmlPlugin.getDefault().fireJmlFinished(file, errors);
			resetResources();
		}

		JmlPropertiesProvider topProps = JmlPropertiesProvider.getPropertiesProvider(ResourceConstants.PLUGIN_DEF_PROPERTIES_FILE);
		boolean msgs = false;
		try {
			msgs = topProps.getBooleanProperty(JmlPluginProperties.STATUS_MESSAGES, file.getProject());
		} catch(CoreException ce) {
			JmlPlugin.getDefault().getLog().log(
			        new Status(IStatus.WARNING, JmlPlugin.PLUGIN_ID,
			                "Problem reading properties file!", ce));
		}

		if( msgs ) {
			if( result ) {
				JmlPlugin.getDefault().getLog().log(
				        new Status(IStatus.INFO, JmlPlugin.PLUGIN_ID,
                                getRunnerName() + ": " + file.getName() + " OK."));
			} else {
				JmlPlugin.getDefault().getLog().log(
				        new Status(IStatus.WARNING, JmlPlugin.PLUGIN_ID,
				                getRunnerName() + ": " + file.getName() + " had problems."));
			}
		}

		return result;
	}

	protected abstract String getRunnerName();

	protected abstract JmlCommonOptions createOptions(IFile file)
            throws CoreException;

	// protected abstract boolean exec(IFile file, JmlCommonOptions jmlo,
    // List<JmlErrorElement> errors) throws CoreException;
    protected abstract boolean exec(String[] arg, JmlCommonOptions jmlOpt,
            ByteArrayOutputStream baos);

    /*
     * Why do we call run on every single file instead of passing all files to
     * MJ/JML at once? The selected files might come from different projects and
     * then need different configurations. To ensure that everything is set up
     * correctly, we need to run each individual file. Because we run MJ/JML in
     * the same process, the overhead should be quite small.
     */
    public boolean run(List<IFile> files, IProgressMonitor monitor) {
		IJmlListener listener = new JmlErrorMarkerCreator(files.get(0).getProject());
		JmlPlugin.getDefault().addListener(listener);

		JmlPlugin.getDefault().fireJmlStartedMultiple();
		boolean status = true;
		Iterator<IFile> iter = files.iterator();

		while (iter.hasNext()) {
			IFile f = iter.next();
			if( !JmlPlugin.isSupportedFileType(f.getName())) continue;

			if( !run(f, monitor)) { status = false; }
		}

		JmlPlugin.getDefault().fireJmlFinishedMultiple();
		JmlPlugin.getDefault().removeListener(listener);
		return status;
	}

	protected boolean run(IProject[] projects, IProgressMonitor monitor)
            throws CoreException {
		// This method is only used to build the projects before a launch.
		// In that situation we do not need an error marker.

		JmlPlugin.getDefault().fireJmlStartedMultiple();
		boolean status = true;
		for (IProject prj : projects) {
			IJavaProject javaProject = JavaCore.create(prj);
			//System.out.println("Project=" + javaProject.getElementName());
			if (!run(javaProject, monitor))	{ status = false; }
		}
		JmlPlugin.getDefault().fireJmlFinishedMultiple();
		return status;
	}

	private boolean run(IJavaProject javaProject, IProgressMonitor monitor)
            throws CoreException {
		boolean status = true;
		IPackageFragmentRoot[] packFragRoot =  javaProject.getAllPackageFragmentRoots();
		for (IPackageFragmentRoot pfr : packFragRoot) 	{
			//System.out.println("PackageFragmentRoot=" + packFragRoot[i].getElementName());
			if (pfr.getKind() == IPackageFragmentRoot.K_SOURCE) {
				if (!run(pfr, monitor)) { status = false; }
			}
		}
		return status;
	}

	private boolean run(IPackageFragmentRoot packFragRoot,
            IProgressMonitor monitor) throws CoreException {
		boolean status = true;
		IJavaElement[] elements = packFragRoot.getChildren();
		for (IJavaElement elem : elements) {
			//System.out.println("Package=" + elements[i].getElementName());
			if (elem.getElementType() == IJavaElement.PACKAGE_FRAGMENT)
			{
				if (!run((IPackageFragment)elem, monitor)) { status = false; }
			}
		}
		return status;
	}

	private boolean run(IPackageFragment packFragment, IProgressMonitor monitor)
            throws CoreException {
		boolean status = true;
		IJavaElement[] compUnits = packFragment.getChildren();
		for (IJavaElement compU : compUnits) {
			//System.out.println("CompilationUnit=" + compUnits[i].getElementName());
			if (compU.getElementType() == IJavaElement.COMPILATION_UNIT) {
				IResource res = ((ICompilationUnit)compU).getUnderlyingResource();
				if (res.getType() == IResource.FILE) {
					IFile file = (IFile)res;
					// System.out.println("Running file: " + file);
					if( !JmlPlugin.isSupportedFileType(file.getName())) continue;

					if (!run(file, monitor)) { status = false; }
				}
			}
		}
		return status;
	}

	private static boolean parseOutput(ByteArrayOutputStream baos, IFile file,
            List<JmlErrorElement> result) {
		boolean okey = true;
		String sep = System.getProperty("line.separator");
		String[] lines = baos.toString().split(sep);
		String ref = null;
		StringBuffer specmsgs = new StringBuffer();
		String actline;

		//DEBUG System.out.println("----------");
		for (String curline : lines) {
			// DEBUG System.out.println(lines[i]);
			if (curline.startsWith("File \"")) {
				int index = curline.lastIndexOf("[");  // left bracket of the JLS reference
				if ( index != -1) {
					ref = curline.substring(index);
					actline = curline.substring(0, curline.lastIndexOf("["));
				} else {
					ref = null;
					actline = curline;
				}

				String[] errorParts = actline.split(",");
				int lineNr = 0; int charNr = 0;
				if (errorParts.length >= 3) {

					IFile actualfile = null;
					{   // code to find the IFile for the error
						String curDir = System.getProperty("user.dir");
						String errorfilepath = curDir
							+ IPath.SEPARATOR
							+ errorParts[0].substring(6, errorParts[0].length()-1);

						try {
						    // try to normalize the path
                            errorfilepath = new java.io.File(errorfilepath).getCanonicalPath();
                        } catch (IOException e1) {
                            // ignore, just use whatever String we had before
                        }

						IProject prj = file.getProject();
						IPath ws = prj.getWorkspace().getRoot().getLocation();
						IPath prjroot = prj.getFullPath();
						String fsprjroot = ws.toOSString() + prjroot.toOSString();

						// on Windows the relative paths from the JML compiler
						// seem to get confused to what drive they belong.
						// then matching agains the workspace directory fails.
						// Just drop the drive letter.
						// TODO: total hack, what better solution is there?
						if (System.getProperty("os.name").startsWith("Windows")) {
						    errorfilepath = errorfilepath.substring(1);
						    fsprjroot = fsprjroot.substring(1);
						}

						if( errorfilepath.startsWith(fsprjroot)) {
							String relpath = errorfilepath.substring(fsprjroot.length());

							IResource r = prj.findMember(relpath);

							if (r != null && r instanceof IFile) {
								actualfile = (IFile) r;
							} else {
								// maybe the file is in a different project or
								// not found.
							    // output the path that the compiler gave, but use
							    // the original file resource.
							    JmlPlugin.getDefault().getLog().log(
							            new Status(IStatus.WARNING, JmlPlugin.PLUGIN_ID,
							                    "Unknown workspace resource in compiler message: " + curline));
								actualfile = file;

							    // TODO: sometimes the line number is too large for this
							    // original file -> also change number.
							}
						} else {
						    String specs = ResourceProvider.getPath(ResourceConstants.JML_SPECS_PATH_NAME);

						    if (specs!=null && errorfilepath.startsWith(specs)) {
						        // usually, the specification files do not create messages
						        // only if the warning pickiness is at a high level, there
						        // might be messages.
						        // We do not add them to the JML2 errors, just make a
						        // log entry.
						        // TODO: these files are not in any of the user's projects.
						        // therefore, we cannot create an IFile for them.
						        // Maybe adapt JmlErrorElement to support "java.io.File".
						        specmsgs.append(curline + sep);
						        continue;
						    } else {
						        // again, file must be somewhere else...
                                // output the path that the compiler gave, but use
                                // the original file resource.
                                JmlPlugin.getDefault().getLog().log(
                                        new Status(IStatus.WARNING, JmlPlugin.PLUGIN_ID,
                                                "Unknown resource in compiler message: " + curline));
						        actualfile = file;
						    }
						}
					}

					lineNr = Integer.parseInt(errorParts[1].substring(6, errorParts[1].length()));
					String[] errorPart2Parts = errorParts[2].split(" ");
					charNr = Integer.parseInt(errorPart2Parts[2]);
					StringBuffer sb = new StringBuffer();

					for (int k = 3; k < errorPart2Parts.length; k++) {
						sb.append(errorPart2Parts[k]);
						sb.append(" ");
					}

					for (int j = 3; j < errorParts.length; j++) {
						sb.append(errorParts[j]);
						// TODO: check whether we should add a "," here
					}

					JmlErrorElement e = new JmlErrorElement(lineNr, charNr, sb.toString(), actualfile, ref);
					okey = false;
					result.add(e);
				} else {
					JmlErrorElement e = new JmlErrorElement(lineNr, charNr, actline, file, ref);
					okey = false;
					result.add(e);
				}
			} else if (curline.startsWith("error:")) {
				JmlErrorElement e = new JmlErrorElement(0, 0, curline, file, null);
				okey = false;
				result.add(e);
			} else if (curline.startsWith("warning:")
			        || curline.startsWith("caution:")
			        || curline.startsWith("notice:")) {
				JmlErrorElement e = new JmlErrorElement(0, 0, curline, file, null);
				result.add(e);
			} else if (curline.startsWith("parsing") ||
					curline.startsWith("typechecking")) {
				// ignore
			} else {
				String msg = "JML2 Eclipse plug-in got unknown compiler message: " + curline;
				JmlErrorElement e = new JmlErrorElement(0, 0, msg, file, null);
				System.out.println(msg);
				okey = false;
				result.add(e);
			}
		}

		if (specmsgs.length() > 0) {
		    JmlPlugin.getDefault().getLog().log(
		            new Status(IStatus.INFO, JmlPlugin.PLUGIN_ID,
		                    "JML specifications produced the following message(s): " + sep
		                    + specmsgs.toString()));
		}

		// DEBUG System.out.println("----------");
		return okey;
	}

	/*
	protected void clearJmlState() {
		org.multijava.util.classfile.ClassPath.initSession();
		org.multijava.mjc.TypeLoader.getSingleton().initSession();
		org.jmlspecs.checker.JmlTypeLoader.getSingleton().initSession();
		org.jmlspecs.checker.JmlTypeLoader.getJmlSingleton().initSession();
	}
	*/

	/** This method tries to re-initialize the resources plugin.
	 * Unfortunately, this is currently necessary, as the JML2 compiler keeps some
	 * state between runs that is not cleared correctly.
	 */
	protected void resetResources() {
		/*
		try {
			Bundle b = Platform.getBundle(JmlResourcesPlugin.PLUGIN_ID);
			String loc = b.getLocation();
			b.stop();
			b.uninstall();

			b = PlatformActivator.getContext().installBundle(loc);
			// b = Platform.getBundle(JmlResourcesPlugin.PLUGIN_ID);
			b.start();
		} catch (Exception e) {
			JmlPlugin.getDefault().getLog().log(new Status(IStatus.ERROR,JmlPlugin.PLUGIN_ID,0,e.toString(),e));
		}
		*/
	}
}
