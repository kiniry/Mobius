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

package ch.ethz.inf.pm.jml.plugin.resources;

import java.io.IOException;
import java.net.URL;

import org.eclipse.core.runtime.FileLocator;
import org.eclipse.core.runtime.IPath;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Path;
import org.eclipse.core.runtime.Platform;
import org.eclipse.core.runtime.Status;
import org.osgi.framework.Bundle;

/**
 * @author Paolo Bazzi
 *
 */
public class ResourceProvider {

	/**
     * Finds file in JML Resources Plugin and returns os-specific path to it
     *
     * @return os-specific path to file
     */
    static public String getPath(String file) {
		Bundle bundle = Platform.getBundle(ResourceConstants.JML_RESOURCES_PLUGIN_NAME);
		IPath path = new Path(file);
        URL jarURL = FileLocator.find(bundle, path, null);
        IPath location = null;
		try {
			location = new Path(FileLocator.resolve(jarURL).getPath());
		} catch (IOException e) {
			JmlResourcesPlugin.getDefault().getLog().log(new Status(IStatus.ERROR,JmlResourcesPlugin.PLUGIN_ID,0,e.getMessage(),e));
			return null;
		}
        return location.toOSString();
    }
}
