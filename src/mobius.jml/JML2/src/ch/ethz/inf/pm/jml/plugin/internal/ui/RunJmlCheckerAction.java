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

package ch.ethz.inf.pm.jml.plugin.internal.ui;

import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IProgressMonitor;

import ch.ethz.inf.pm.jml.plugin.internal.core.JmlCheckerRunner;

/**
 * @author Paolo Bazzi
 * @author WMD
 */
public class RunJmlCheckerAction extends RunAction {
	@Override
	protected String getActionName() {
		return "JML2 checker";
	}

	@Override
	protected void runAction(IProgressMonitor monitor) throws CoreException {
		// JmlPlugin.getDefault().runChecker(getFiles(), monitor);
		new JmlCheckerRunner().run(getFiles(), monitor);
	}


	/*
	void old() {
		ProgressMonitorDialog dialog= new ProgressMonitorDialog(getShell());
		try {
			dialog.run(true, true, new IRunnableWithProgress() {
				public void run(IProgressMonitor monitor) throws InvocationTargetException {
					try {
						JmlPlugin.getDefault().runChecker(getFiles());
					} catch (CoreException e) {
						throw new InvocationTargetException(e);
					}
				}
			});
		} catch (InterruptedException e) {
			ErrorDialog.openError(getShell(), "Error", "Error executing JML Checker", new Status(IStatus.ERROR, JmlPlugin.PLUGIN_ID, 0,e.getMessage(),null));
		} catch (InvocationTargetException e) {
			Throwable t = e.getTargetException();
			if (t instanceof CoreException)
			{
				ErrorDialog.openError(getShell(), "Error", "Error executing JML Checker", ((CoreException)t).getStatus());
			} else {
				ErrorDialog.openError(getShell(), "Error", "Error executing JML Checker", new Status(IStatus.ERROR, JmlPlugin.PLUGIN_ID, 0,e.getTargetException().getMessage(),null));
			}
		}
	}
	*/
}
