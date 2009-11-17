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


package ch.ethz.inf.pm.jml.plugin.internal.ui.errors;

import java.util.Iterator;
import java.util.List;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IMarker;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Status;

import ch.ethz.inf.pm.jml.plugin.IJmlListener;
import ch.ethz.inf.pm.jml.plugin.JmlErrorElement;
import ch.ethz.inf.pm.jml.plugin.internal.core.JmlPlugin;

/**
 * @author Paolo Bazzi
 *
 */

public class JmlErrorMarkerCreator implements IJmlListener {
	private final static String MARKER_ID = JmlPlugin.PLUGIN_ID + ".error";

	private final IProject project;

	public JmlErrorMarkerCreator(IProject project) {
		this.project = project;
	}

	public void jmlStarted(IFile file) {
		try {
			file.deleteMarkers(MARKER_ID, false, IResource.DEPTH_INFINITE);
		} catch (CoreException e) {
			JmlPlugin.getDefault().getLog().log(new Status(IStatus.ERROR,JmlPlugin.PLUGIN_ID,0,e.toString(),e));
		}
	}

	public void jmlFinished(IFile file, List<JmlErrorElement> result) {
		if (!file.getProject().equals(this.project)) return;

		try {
			Iterator<JmlErrorElement> iter = result.iterator();
			while (iter.hasNext()) {
				JmlErrorElement e = iter.next();

				IMarker marker = e.getFile().createMarker(MARKER_ID);
				marker.setAttribute(IMarker.SEVERITY, Integer.valueOf(IMarker.SEVERITY_WARNING));
				marker.setAttribute(IMarker.LINE_NUMBER, Integer.valueOf(e.getLineNr()));
				marker.setAttribute(IMarker.MESSAGE, "JML2 " + e.getMessage());
			}
		} catch (CoreException e1) {
			// e1.printStackTrace();
			JmlPlugin.getDefault().getLog().log(new Status(IStatus.ERROR,JmlPlugin.PLUGIN_ID,0,e1.toString(),e1));
		}
	}

	public void jmlFinishedMultiple() {
		// Nothing to do...
	}

	public void jmlStartedMultiple() {
		// Nothing to do...
	}
}
