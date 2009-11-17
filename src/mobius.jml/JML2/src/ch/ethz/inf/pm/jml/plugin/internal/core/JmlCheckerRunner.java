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

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Status;
import org.eclipse.jdt.core.IClasspathEntry;
import org.eclipse.jdt.core.IJavaProject;
import org.eclipse.jdt.core.JavaCore;
import org.eclipse.jdt.core.JavaModelException;
import org.jmlspecs.checker.JmlCommonOptions;
import org.jmlspecs.checker.JmlOptions;

import ch.ethz.inf.pm.jml.plugin.internal.core.properties.JmlCheckerProperties;
import ch.ethz.inf.pm.jml.plugin.internal.core.properties.JmlPropertiesProvider;
import ch.ethz.inf.pm.jml.plugin.resources.ResourceConstants;
import ch.ethz.inf.pm.jml.plugin.resources.ResourceProvider;


/**
 * @author Paolo Bazzi
 * @author WMD
 */
public class JmlCheckerRunner extends JmlRunner {
	@Override
	protected String getRunnerName() {
		return "JML2 checker";
	}

	/* The return type is only JmlCommonOptions to allow the subclass JmlCompilerRunner.
	 * The actual return type is JmlOptions.
	 *
	 * (non-Javadoc)
	 * @see ch.ethz.inf.pm.jml.plugin.internal.core.JmlRunner#createOptions(org.eclipse.core.resources.IFile)
	 */
	@Override
	protected JmlCommonOptions createOptions(IFile file) throws CoreException {
		JmlOptions jmlo = new JmlOptions();
		IProject proj = file.getProject();

		setCheckerProperties(jmlo, proj);

		return jmlo;
	}

	@Override
	protected boolean  exec(String[] arg, JmlCommonOptions jmlComOpt, ByteArrayOutputStream baos) {
		JmlOptions jmlOpt = (JmlOptions) jmlComOpt;
		return org.jmlspecs.checker.Main.compile(arg, jmlOpt, baos);
	}

	protected void setCheckerProperties(JmlCommonOptions jmlo, IProject proj)
	throws CoreException {
		JmlPropertiesProvider checkerProps = JmlPropertiesProvider.getPropertiesProvider(ResourceConstants.CHECKER_DEF_PROPERTIES_FILE);

		jmlo.set_admissibility(checkerProps.getProperty(JmlCheckerProperties.ADMISSIBILITY,proj));
		jmlo.set_assignable(checkerProps.getBooleanProperty(JmlCheckerProperties.aSSIGNABLE,proj));
		jmlo.set_Assignable(checkerProps.getBooleanProperty(JmlCheckerProperties.ASSIGNABLE,proj));
		jmlo.set_debug(checkerProps.getBooleanProperty(JmlCheckerProperties.DEBUG,proj));
		jmlo.set_defaultNonNull(checkerProps.getBooleanProperty(JmlCheckerProperties.DEFAULT_NON_NULL,proj));
		jmlo.set_deprecation(checkerProps.getBooleanProperty(JmlCheckerProperties.DEPRECATION,proj));
		String excludeFile = checkerProps.getProperty(JmlCheckerProperties.EXCLUDE_FILES,proj);
		if (excludeFile != null && !excludeFile.equalsIgnoreCase("")) { jmlo.set_excludefiles(excludeFile); }
		String experiment = checkerProps.getProperty(JmlCheckerProperties.EXPERIMENT,proj);
		if (experiment != null && !experiment.equalsIgnoreCase("")) { jmlo.set_experiment(experiment); }
		String filter = checkerProps.getProperty(JmlCheckerProperties.FILTER,proj);
		if (filter != null && !filter.equalsIgnoreCase("")) { jmlo.set_filter(filter); }
		String xlint = checkerProps.getProperty(JmlCheckerProperties.XLINT,proj);
		if (xlint != null && !xlint.equalsIgnoreCase("")) { jmlo.set_Xlint(xlint); }
		jmlo.set_generic(checkerProps.getBooleanProperty(JmlCheckerProperties.GENERIC,proj));
		jmlo.set_keepGoing(checkerProps.getBooleanProperty(JmlCheckerProperties.KEEP_GOING,proj));
		jmlo.set_multijava(checkerProps.getBooleanProperty(JmlCheckerProperties.MULTIJAVA,proj));
		jmlo.set_nonnull(checkerProps.getBooleanProperty(JmlCheckerProperties.NON_NULL,proj));
		jmlo.set_nonnulltypes(checkerProps.getBooleanProperty(JmlCheckerProperties.NON_NULL_TYPES,proj));
		jmlo.set_xArrayNNTS(checkerProps.getBooleanProperty(JmlCheckerProperties.XARRAY_NNTS,proj));
		jmlo.set_purity(checkerProps.getBooleanProperty(JmlCheckerProperties.PURITY,proj));
		jmlo.set_Quiet(checkerProps.getBooleanProperty(JmlCheckerProperties.QUIET,proj));
		jmlo.set_quiet(checkerProps.getBooleanProperty(JmlCheckerProperties.qUIET,proj));
		jmlo.set_recursive(checkerProps.getBooleanProperty(JmlCheckerProperties.RECURSIVE,proj));
		jmlo.set_relaxed(checkerProps.getBooleanProperty(JmlCheckerProperties.RELAXED,proj));
		jmlo.set_safemath(checkerProps.getBooleanProperty(JmlCheckerProperties.SAFE_MATH,proj));
		String source = checkerProps.getProperty(JmlCheckerProperties.SOURCE,proj);
		if (source != null && !source.equalsIgnoreCase("")) { jmlo.set_source(source); }

		// a easy mistake is to write "parse, check" with a space, instead of
		// leaving the space away. Fix this automatically.
		String univx = checkerProps.getProperty(JmlCheckerProperties.UNIVERSESX,proj);
		univx = univx.replace(" ", "");
		jmlo.set_universesx(univx);

		jmlo.set_UnsafeOpWarnings(checkerProps.getBooleanProperty(JmlCheckerProperties.UNSAFE_OP_WARNINGS,proj));
		jmlo.set_verbose(checkerProps.getBooleanProperty(JmlCheckerProperties.VERBOSE,proj));
		jmlo.set_warning(checkerProps.getIntProperty(JmlCheckerProperties.WARNING,proj));

		String workingDir = proj.getLocation().toOSString();

		String outDir = getDestination(checkerProps.getProperty(JmlCheckerProperties.DESTINATION, proj), workingDir);
		jmlo.set_destination(outDir);

		String classPath = getClasspath(checkerProps.getProperty(JmlCheckerProperties.CLASSPATH,proj), proj);
		jmlo.set_classpath(classPath);

		setSource(jmlo, checkerProps.getProperty(JmlCheckerProperties.SOURCE_PATH,proj), classPath, workingDir);
	}


	private static void setSource(JmlCommonOptions opts, String propSrc, String classPath, String workingDir) {
		// add source path
		String sourcePath = propSrc;
		if (sourcePath != null && !sourcePath.equalsIgnoreCase("")) {
			sourcePath = sourcePath + ResourceConstants.PATH_SEPARATOR + classPath;
			opts.set_sourcepath(sourcePath);
			// DEBUG System.out.println("sourcePath: " + sourcePath);
		} else {
			// if the user doesn't provide a source path, we do not need to set it.
			// JML2 automatically uses the classpath.
			// sourcePath = workingDir + ResourceConstants.FILE_SEPARATOR + ResourceConstants.DEFAULT_SRC;
		}
	}

	public static String getDestination(String propDir, String workingDir) {
		// get destination
		String outDir = propDir;
		if (outDir != null && !outDir.equalsIgnoreCase("")) {
			if (! (new java.io.File(outDir).exists()) ) {
				outDir = workingDir + ResourceConstants.FILE_SEPARATOR + outDir;
			}
		} else {
			// use a default
			outDir = workingDir + ResourceConstants.FILE_SEPARATOR + ResourceConstants.DEFAULT_OUT;
		}
		// DEBUG System.out.println("outDir: " + outDir);
		return outDir;
	}

	private static String getProjectClasspath(IProject proj) throws CoreException {
		String workspaceDir = proj.getWorkspace().getRoot().getLocation().toOSString();

		IClasspathEntry[] cp = null;
		try {
			IJavaProject jproj = JavaCore.create(proj);
			cp = jproj.getResolvedClasspath(true);
		} catch( JavaModelException me ) {
			// the project is not a Java project and we cannot get a classpath.
			return null;
		}
		String scp = null;

		for(IClasspathEntry cpe : cp) {
			String complete = cpe.getPath().toOSString();

			if( !(new java.io.File(complete).exists()) ) {
				complete = workspaceDir + complete;
			}
			if( new java.io.File(complete).exists() ) {
				if(scp==null) {
					scp = complete;
				} else {
					scp = scp + ResourceConstants.PATH_SEPARATOR + complete;
				}
			} else {
				JmlPlugin.getDefault().getLog().log( new Status(IStatus.WARNING, JmlPlugin.PLUGIN_ID,
						"Could not resolve classpath entry: " + cpe.getPath().toOSString()
						+ " also not as: " + complete));
			}
		}

		return scp;
	}

	private static String jmlClasspath = null;

	private static String getJmlClasspath() throws CoreException
	{
		if (jmlClasspath == null) {
			String jmlrelease = ResourceProvider.getPath(ResourceConstants.JML_RELEASE_LIBRARY_NAME);
			String jmlspecs = ResourceProvider.getPath(ResourceConstants.JML_SPECS_PATH_NAME);

			if (jmlrelease == null || jmlspecs == null) {
				throw new CoreException(
						new Status(IStatus.ERROR, JmlPlugin.PLUGIN_ID, "Could not get JML2 classpath from jml-resources plug-in."));
			}
			jmlClasspath = jmlspecs + ResourceConstants.PATH_SEPARATOR + jmlrelease;
		}
		return jmlClasspath;
	}

	public static String getClasspath(String propCp, IProject proj) throws CoreException {
		// add project classpath & JML2 jar & specs to classpath
		String classPath = null;
		if (propCp != null && !propCp.equalsIgnoreCase("")) {
			classPath = propCp;
		}

		String pcp = getProjectClasspath(proj);
		if ( pcp != null && !pcp.equalsIgnoreCase("") ) {
			if( classPath != null ) {
				classPath = classPath + ResourceConstants.PATH_SEPARATOR + pcp;
			} else {
				classPath = pcp;
			}
		}
		if( classPath != null ) {
			classPath = classPath + ResourceConstants.PATH_SEPARATOR + getJmlClasspath();
		} else {
			classPath = getJmlClasspath();
		}

		// DEBUG System.out.println("CP = " + opts.classpath());
		return classPath;
	}

	/*
	private boolean exec(IFile file, JmlOptions jmlo, List<JmlErrorElement> errors) {
		ByteArrayOutputStream baos = new ByteArrayOutputStream();
        String[] arg = new String[] { file.getLocation().toOSString() };

	    try {
			// Get the directory (URL) of the reloadable class
		    java.net.URL[] urls = null;
		    String jmljar = ch.ethz.inf.pm.jml.plugin.resources.ResourceProvider.getPath(ResourceConstants.JML_RELEASE_LIBRARY_NAME);

	        // Convert the file object to a URL
	        java.io.File dir = new java.io.File(jmljar);
	        urls = new java.net.URL[]{ dir.toURI().toURL() };

	        // Create a new class loader with the directory
	        ClassLoader cl = new java.net.URLClassLoader(urls);

	        // Load in the class
	        Class<?> cls = cl.loadClass("org.jmlspecs.checker.Main");
			// Class<?>[] argT = new Class<?>[] { String[].class, JmlOptions.class, OutputStream.class };
			// java.lang.reflect.Method m = cls.getMethod("compile", argT);
	        java.lang.reflect.Method m = cls.getMethod("main", new Class[] {String[].class});
			m.invoke(null, arg,jmlo,baos);

	    } catch (java.net.MalformedURLException e) {
	    	e.printStackTrace();
	    } catch (IllegalAccessException e) {
	    	e.printStackTrace();
	    } catch (ClassNotFoundException e) {
	    	e.printStackTrace();
	    } catch (SecurityException e) {
			// TODO Auto-generated catch block
	    	e.printStackTrace();
		} catch (NoSuchMethodException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		} catch (IllegalArgumentException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		} catch (InvocationTargetException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}

		boolean result = parseOutput(baos, file, errors);
		try {
			baos.close();
		} catch (IOException e) {
			JmlPlugin.getDefault().getLog().log(new Status(IStatus.ERROR,JmlPlugin.PLUGIN_ID,0,e.getMessage(),e));
		}
		return result;
	}
	*/

	/*
	@Override
	protected boolean exec(IFile file, JmlCommonOptions jmlo, List<JmlErrorElement> errors) {
		ByteArrayOutputStream baos = new ByteArrayOutputStream();
        String[] arg = new String[] { file.getLocation().toOSString() };

		try {
			org.jmlspecs.checker.Main.compile(arg,jmlo,baos);
		} catch (Throwable e) {
			// org.jmlspecs.checker.Main.bugReportRequest(e,arg);
			JmlPlugin.getDefault().getLog().log(new Status(IStatus.ERROR,JmlPlugin.PLUGIN_ID,0,e.toString(),e));
		}

		boolean result = parseOutput(baos, file, errors);
		try {
			baos.close();
		} catch (IOException e) {
			JmlPlugin.getDefault().getLog().log(new Status(IStatus.ERROR,JmlPlugin.PLUGIN_ID,0,e.getMessage(),e));
		}
		return result;
	}
	*/
}
