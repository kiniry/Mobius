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

import java.io.File;
import java.util.ArrayList;
import java.util.List;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Status;
import org.eclipse.debug.core.ILaunchConfiguration;
import org.eclipse.jdt.core.IJavaProject;
import org.eclipse.jdt.core.IType;
import org.eclipse.jdt.core.JavaCore;
import org.eclipse.jdt.launching.IRuntimeClasspathEntry;
import org.eclipse.jdt.launching.JavaLaunchDelegate;
import org.eclipse.jdt.launching.JavaRuntime;

import ch.ethz.inf.pm.jml.plugin.internal.core.properties.JmlCheckerProperties;
import ch.ethz.inf.pm.jml.plugin.internal.core.properties.JmlPropertiesProvider;
import ch.ethz.inf.pm.jml.plugin.internal.core.properties.JmlRacProperties;
import ch.ethz.inf.pm.jml.plugin.resources.ResourceConstants;
import ch.ethz.inf.pm.jml.plugin.resources.ResourceProvider;

/**
 * @author Paolo Bazzi
 * @author Andreas Fuerer
 * @author WMD
 */
public class JmlRacLaunchConfigurationDelegate extends JavaLaunchDelegate {
	public static final String JML_RAC_CONFIGURATION_TYPE = "ch.ethz.inf.pm.jml.plugin.LaunchConfiguration.JmlRac";
	public static final String ATTR_AUTO_BUILD = JmlRacProperties.AUTO_BUILD;

	/* (non-Javadoc)
	 * @see org.eclipse.jdt.launching.AbstractJavaLaunchConfigurationDelegate#getVMArguments(org.eclipse.debug.core.ILaunchConfiguration)
	 */
	@Override
	public String getVMArguments(ILaunchConfiguration configuration) throws CoreException {
		StringBuffer arguments = new StringBuffer(super.getVMArguments(configuration));

		arguments.append(" "); //$NON-NLS-1$
		arguments.append("-Xbootclasspath/a:\"" + ResourceProvider.getPath(ResourceConstants.JML_RELEASE_LIBRARY_NAME) +"\"");
		return arguments.toString();
	}

	/* (non-Javadoc)
	 * @see org.eclipse.jdt.launching.AbstractJavaLaunchConfigurationDelegate#getClasspath(org.eclipse.debug.core.ILaunchConfiguration)
	 */
	@Override
	public String[] getClasspath(ILaunchConfiguration configuration) throws CoreException {
		IRuntimeClasspathEntry[] entries = JavaRuntime.computeUnresolvedRuntimeClasspath(configuration);
		entries = JavaRuntime.resolveRuntimeClasspath(entries, configuration);
		List<String> userEntries = new ArrayList<String>(entries.length);

		for ( IRuntimeClasspathEntry entry : entries) {
			if (entry.getClasspathProperty() == IRuntimeClasspathEntry.USER_CLASSES) {
				String location = entry.getLocation();
				if (entry.getType() == IRuntimeClasspathEntry.PROJECT)
				{
					IJavaProject entryPro = (IJavaProject) JavaCore.create(entry.getResource());
					IJavaProject configurationPro = getJavaProject(configuration);
					if (entryPro.equals(configurationPro))
					{
						String workingDir = configurationPro.getProject().getLocation().toOSString();
						JmlPropertiesProvider props = JmlPropertiesProvider.getPropertiesProvider(ResourceConstants.CHECKER_DEF_PROPERTIES_FILE);
						String outDir = props.getProperty(JmlCheckerProperties.DESTINATION, configurationPro.getProject());

						location = JmlCheckerRunner.getDestination(outDir, workingDir);
						// DEBUG System.out.println("Class location for RT CP = " + location);
					}
				}
				if (location != null) {
					userEntries.add(location);
				}
			}
		}

		// add runtime library to classpath in order to allow Universe RT checks
		userEntries.add(ResourceProvider.getPath(ResourceConstants.JML_RELEASE_LIBRARY_NAME));

		return userEntries.toArray(new String[userEntries.size()]);
	}

	@Override
	public boolean preLaunchCheck(ILaunchConfiguration configuration, String mode, IProgressMonitor monitor) throws CoreException {
		String mainClass = getMainTypeName(configuration);
		if (mainClass.indexOf(".") != -1) {
			mainClass = mainClass.replace(".",ResourceConstants.FILE_SEPARATOR);
		}
		JmlPropertiesProvider racprops = JmlPropertiesProvider.getPropertiesProvider(ResourceConstants.RAC_DEF_PROPERTIES_FILE);
		boolean autoBulid = configuration.getAttribute(JmlRacLaunchConfigurationDelegate.ATTR_AUTO_BUILD, racprops.getBooleanDefaultProperty(JmlRacProperties.AUTO_BUILD));
		if (!autoBulid) {
			IJavaProject jproj = getJavaProject(configuration);
			if (jproj == null) {
				throw new CoreException(new Status(IStatus.ERROR,JmlPlugin.PLUGIN_ID,0,"Cannot launch project without Java nature.",null));
			}
			IProject project = jproj.getProject();

			JmlPropertiesProvider checkerprops = JmlPropertiesProvider.getPropertiesProvider(ResourceConstants.CHECKER_DEF_PROPERTIES_FILE);

			String destFolder = checkerprops.getProperty(JmlCheckerProperties.DESTINATION, project);
			String workingDir = project.getLocation().toOSString();
			String location = JmlCheckerRunner.getDestination(destFolder, workingDir);

			File classFile = new File( location + ResourceConstants.FILE_SEPARATOR  + mainClass + ".class");
			if (!classFile.exists()) {
				// DEBUG System.out.println("class file not found!");
				IType type = jproj.findType(getMainTypeName(configuration));
				IResource res = type.getUnderlyingResource();
				if (res.getType() == IResource.FILE) {
					IFile file = (IFile)res;
					List<IFile> files = new ArrayList<IFile>(1);
					files.add(file);
					boolean ok = new JmlCompilerRunner().run(files, monitor);
					if (!ok) throw new CoreException(new Status(IStatus.ERROR,JmlPlugin.PLUGIN_ID,0,"Error building project, cannot launch.",null));
				}
			}
		}
		return super.preLaunchCheck(configuration, mode, monitor);
	}

	@Override
	public boolean buildForLaunch(ILaunchConfiguration configuration, String mode, IProgressMonitor monitor) throws CoreException {
		boolean res = super.buildForLaunch(configuration, mode, monitor);

		JmlPropertiesProvider props = JmlPropertiesProvider.getPropertiesProvider(ResourceConstants.RAC_DEF_PROPERTIES_FILE);
		boolean autoBulid = configuration.getAttribute(JmlRacLaunchConfigurationDelegate.ATTR_AUTO_BUILD, props.getBooleanDefaultProperty(JmlRacProperties.AUTO_BUILD));
		if (autoBulid) {
			// DEBUG System.out.println("Start Auto Bulid");
			IProject[] projects = getBuildOrder(configuration, mode);
			if (projects != null) {
				boolean result = new JmlCompilerRunner().run(projects, monitor);
				if (!result) {
					// DEBUG System.out.println("Error compiling classes");
					throw new CoreException(new Status(IStatus.ERROR,JmlPlugin.PLUGIN_ID,0,"Error building project.",null));
				}
			}
		}
		return res;
	}
}