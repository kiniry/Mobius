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

package ch.ethz.inf.pm.jml.plugin.internal.core.properties;

import java.io.FileInputStream;
import java.io.IOException;
import java.util.HashMap;
import java.util.Map;
import java.util.Properties;

import org.eclipse.core.resources.IProject;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.QualifiedName;
import org.eclipse.core.runtime.Status;

import ch.ethz.inf.pm.jml.plugin.internal.core.JmlPlugin;
import ch.ethz.inf.pm.jml.plugin.resources.ResourceProvider;

/**
 * @author Paolo Bazzi
 *
 */
public class JmlPropertiesProvider {
	private final Properties checkerProps = new Properties();
	private boolean ready = false;

	// singleton implementation
	private static final Map<String,JmlPropertiesProvider> propProvider = new HashMap<String,JmlPropertiesProvider>();

	public static JmlPropertiesProvider getPropertiesProvider(String props) {
		if (!propProvider.containsKey(props)) {
			propProvider.put(props, new JmlPropertiesProvider(props));
		}
		return propProvider.get(props);
	}

	private JmlPropertiesProvider(String propFile)
	{
		String filePath = ResourceProvider.getPath(propFile);
		FileInputStream in = null;
		try {
			in = new FileInputStream(filePath);
			checkerProps.load(in);
			ready = true;
		} catch (IOException e) {
			JmlPlugin.getDefault().getLog().log(
					new Status(IStatus.ERROR, JmlPlugin.PLUGIN_ID, 0, e.getMessage(), e));
		} finally {
			if (in != null) {
				try {
					in.close();
				} catch (IOException e) {
					JmlPlugin.getDefault().getLog().log(
							new Status(IStatus.ERROR, JmlPlugin.PLUGIN_ID, 0, e.getMessage(), e));
				}
			}
		}
	}

	private boolean isReady() {
		return ready;
	}

	private IStatus getStatus(String msg) {
		return new Status(IStatus.ERROR,JmlPlugin.PLUGIN_ID,0,msg,null);
	}

	private IStatus getStatus(String msg, Exception e) {
		return new Status(IStatus.ERROR,JmlPlugin.PLUGIN_ID,0,msg,e);
	}

	public String getProperty(String key, IProject project) throws CoreException
	{
		String value = null;
		try {
			value = project.getPersistentProperty(new QualifiedName(JmlPlugin.PLUGIN_ID,key));
		} catch (CoreException e) {
			throw new CoreException(getStatus("Error getting project property",e));
		}
		if (value == null)
		{
			value = getDefaultProperty(key);
		}
		return value;
	}

	public String getDefaultProperty(String key) throws CoreException {
		if (!isReady()) throw new CoreException(getStatus("Error loading default properties file"));
		return checkerProps.getProperty(key);
	}

	public boolean getBooleanProperty(String key, IProject project) throws CoreException {
		return Boolean.valueOf(getProperty(key,project));
	}

	public boolean getBooleanDefaultProperty(String key) throws CoreException 	{
		if (!isReady()) throw new CoreException(getStatus("Error loading default properties file"));
		return Boolean.valueOf(checkerProps.getProperty(key));
	}

	public int getIntProperty(String key, IProject project) throws CoreException 	{
		String value = getProperty(key, project);
		int res = 0;
		try {
			res = Integer.parseInt(value);
		} catch (NumberFormatException e)  {
			throw new CoreException(getStatus("Error parsing int value from project properties",e));
		}
		return  res;
	}

	public int getIntDefaultProperty(String key) throws CoreException {
		if (!isReady()) throw new CoreException(getStatus("Error loading default properties file"));
		String value = checkerProps.getProperty(key);
		int res = 0;
		try {
			res = Integer.parseInt(value);
		} catch (NumberFormatException e)  {
			throw new CoreException(getStatus("Error parsing default int value from properties file",e));
		}
		return  res;
	}
}
