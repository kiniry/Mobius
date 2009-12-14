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

import org.eclipse.core.runtime.Plugin;
import org.osgi.framework.BundleContext;

/**
 * @author Paolo Bazzi
 *
 */
public class JmlResourcesPlugin extends Plugin {
	// The plug-in ID
	public static final String PLUGIN_ID = "ch.ethz.inf.pm.jml.plugin.resources";

	// The shared instance
	private static JmlResourcesPlugin plugin;

	/**
	 * The constructor
	 */
	public JmlResourcesPlugin() {
		plugin = this;
	}

	/**
	 * Returns the shared instance
	 *
	 * @return the shared instance
	 */
	public static JmlResourcesPlugin getDefault() {
		return plugin;
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
}
