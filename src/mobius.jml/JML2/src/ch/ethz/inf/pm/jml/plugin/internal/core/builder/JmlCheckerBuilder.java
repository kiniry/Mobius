/*
 * This file is part of the JML2 Eclipse Plug-in Project.
 *
 * Copyright (C) 2008 Swiss Federal Institute of Technology Zurich
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
 */

package ch.ethz.inf.pm.jml.plugin.internal.core.builder;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.resources.IResourceDelta;
import org.eclipse.core.resources.IResourceDeltaVisitor;
import org.eclipse.core.resources.IResourceVisitor;
import org.eclipse.core.resources.IncrementalProjectBuilder;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Status;

import ch.ethz.inf.pm.jml.plugin.internal.core.JmlCheckerRunner;
import ch.ethz.inf.pm.jml.plugin.internal.core.JmlPlugin;

public class JmlCheckerBuilder extends IncrementalProjectBuilder {

	class JmlCheckerDeltaVisitor implements IResourceDeltaVisitor {
		private final IProgressMonitor monitor;

		public JmlCheckerDeltaVisitor(IProgressMonitor mon) {
			monitor = mon;
		}

		/*
		 * (non-Javadoc)
		 *
		 * @see org.eclipse.core.resources.IResourceDeltaVisitor#visit(org.eclipse.core.resources.IResourceDelta)
		 */
		public boolean visit(IResourceDelta delta) throws CoreException {
			IResource resource = delta.getResource();
			switch (delta.getKind()) {
			case IResourceDelta.ADDED:
				// handle added resource
				checkResource(resource, monitor);
				break;
			case IResourceDelta.REMOVED:
				// handle removed resource
				// ignore this case, would need a full rebuild
				break;
			case IResourceDelta.CHANGED:
				// handle changed resource
				checkResource(resource, monitor);
				break;
			}
			//return true to continue visiting children.
			return true;
		}
	}

	class JmlCheckerResourceVisitor implements IResourceVisitor {
		private final IProgressMonitor monitor;

		public JmlCheckerResourceVisitor(IProgressMonitor mon) {
			monitor = mon;
		}

		public boolean visit(IResource resource) {
			checkResource(resource, monitor);
			//return true to continue visiting children.
			return true;
		}
	}

	public static final String BUILDER_ID = "ch.ethz.inf.pm.jml.plugin.CheckerBuilder";

	/*
	 * (non-Javadoc)
	 *
	 * @see org.eclipse.core.internal.events.InternalBuilder#build(int,
	 *      java.util.Map, org.eclipse.core.runtime.IProgressMonitor)
	 */
	@SuppressWarnings("unchecked")
	@Override
	protected IProject[] build(int kind, Map args, IProgressMonitor monitor) {
		try {
			if (kind == FULL_BUILD) {
				fullBuild(monitor);
			} else {
				IResourceDelta delta = getDelta(getProject());
				if (delta == null) {
					fullBuild(monitor);
				} else {
					incrementalBuild(delta, monitor);
				}
			}
		} catch (CoreException e) {
			JmlPlugin.getDefault().getLog().log( new Status(IStatus.WARNING, JmlPlugin.PLUGIN_ID,
					"A problem occured during JML2 background checking: " + e ));
		}
		return null;
	}

	private void checkResource(IResource resource, IProgressMonitor monitor) {
		if ( resource.getType() == IResource.FILE ) {
			IFile file = (IFile) resource;
			List<IFile> files = new ArrayList<IFile>(1);
			files.add(file);
			// JmlPlugin.getDefault().runChecker(files, monitor);
			boolean status = new JmlCheckerRunner().run(files, monitor);
			if( !status ) {
				JmlPlugin.getDefault().getLog().log( new Status(IStatus.WARNING, JmlPlugin.PLUGIN_ID,
							"A problem occured during JML2 background checking!" ));
			}
		}
	}

	protected void fullBuild(final IProgressMonitor monitor)
			throws CoreException {
		getProject().accept(new JmlCheckerResourceVisitor(monitor));
	}

	protected void incrementalBuild(IResourceDelta delta,
			IProgressMonitor monitor) throws CoreException {
		delta.accept(new JmlCheckerDeltaVisitor(monitor));
	}
}
