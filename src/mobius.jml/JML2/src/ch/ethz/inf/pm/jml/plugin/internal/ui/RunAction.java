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

import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Status;
import org.eclipse.core.runtime.jobs.Job;
import org.eclipse.jdt.core.ICompilationUnit;
import org.eclipse.jdt.core.IImportContainer;
import org.eclipse.jdt.core.IJavaElement;
import org.eclipse.jdt.core.IJavaProject;
import org.eclipse.jdt.core.IPackageDeclaration;
import org.eclipse.jdt.core.IPackageFragment;
import org.eclipse.jdt.core.IPackageFragmentRoot;
import org.eclipse.jdt.core.IType;
import org.eclipse.jdt.core.JavaCore;
import org.eclipse.jface.action.IAction;
import org.eclipse.jface.text.ITextSelection;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.swt.SWT;
import org.eclipse.swt.widgets.Display;
import org.eclipse.swt.widgets.MessageBox;
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.IEditorReference;
import org.eclipse.ui.IFileEditorInput;
import org.eclipse.ui.IObjectActionDelegate;
import org.eclipse.ui.IWorkbenchPage;
import org.eclipse.ui.IWorkbenchPart;
import org.eclipse.ui.IWorkbenchWindow;
import org.eclipse.ui.IWorkbenchWindowActionDelegate;

import ch.ethz.inf.pm.jml.plugin.JmlErrorElement;
import ch.ethz.inf.pm.jml.plugin.internal.core.JmlPlugin;

/**
 * @author Paolo Bazzi
 * @author WMD
 */
public abstract class RunAction implements IObjectActionDelegate, IWorkbenchWindowActionDelegate {
	abstract protected String getActionName();
	abstract protected void runAction(IProgressMonitor monitor) throws CoreException;

	public void run(final IAction action) {
		Job j = new Job("Running " + getActionName()) {
			@Override
			protected IStatus run(IProgressMonitor monitor) {
				return work(action, monitor);
			}
		};
		j.setUser(true);
		j.schedule();

		// if the view is made visible before the job is started,
		// the selection is messed up!
		// so if we do this, do it here.
		// but WMD does not like this behavior anyway, so it's gone.
		// showView(JmlErrorView.ID);
	}


	private IStatus work(IAction action, IProgressMonitor monitor) {
		initFiles();

		try {
			addFiles();
		} catch (CoreException e) {
			return e.getStatus();
		}

		if( getFiles()==null || getFiles().isEmpty() ) {
			IStatus st = new Status(IStatus.ERROR, JmlPlugin.PLUGIN_ID, "Error adding files for the " + getActionName() + ".");
			return st;
		}

		monitor.beginTask(getActionName(), getFiles().size());
		try {
			runAction(monitor);
		} catch (CoreException e) {
			return new Status(IStatus.ERROR, JmlPlugin.PLUGIN_ID, "Error executing " + getActionName() + ".");
		}
		monitor.done();
		return Status.OK_STATUS;
	}

	protected ISelection selection;
	protected IWorkbenchPart workbenchPart;

	public void dispose() {

	}

	public void init(IWorkbenchWindow window) {
		workbenchPart = window.getActivePage().getActivePart();
		this.selection = window.getSelectionService().getSelection();
	}

	public void selectionChanged(IAction action, ISelection selection) {
		if( selection != null &&
				selection instanceof IStructuredSelection )
		this.selection = selection;

		action.setEnabled( enabledForSelection() );
	}

	public void setActivePart(IAction action, IWorkbenchPart targetPart) {
		workbenchPart = targetPart;
		action.setEnabled(enabledForFile(getWorkspaceFile(workbenchPart)));
	}


	private List<IFile> cachedFiles = null;

	private void initFiles() {
		cachedFiles = new ArrayList<IFile>();
	}

	protected List<IFile> getFiles() 	{
		return cachedFiles;
	}

	// keep consistent with addFiles() in order to enable for the correct selections
	private boolean enabledForSelection() {
		// System.out.println("selection: " + selection + ". class: " + selection.getClass());

		if( selection==null || selection.isEmpty() ||
				selection instanceof ITextSelection ) {
		 	return enabledForFile(getWorkspaceFile(workbenchPart));
		} else if( selection instanceof IStructuredSelection ) {
			IStructuredSelection structured = (IStructuredSelection)selection;

			Iterator<?> iter = structured.iterator();
			while (iter.hasNext()) {
				Object obj = iter.next();
				if (obj instanceof IFile) {
					if( enabledForFile((IFile)obj) )
						return true;
				} else if (obj instanceof IJavaProject) {
					// at one point I just used IJavaElement to collect more of the cases
					// below, but this did not work, as some unhandled classes were then
					// enabled...
					return true;
				} else if (obj instanceof IPackageFragmentRoot) {
					return true;
				} else if (obj instanceof IPackageFragment) {
					return true;
				} else if (obj instanceof ICompilationUnit) {
					return true;
				} else if (obj instanceof IType) {
					return true;
				} else if (obj instanceof IPackageDeclaration) {
					return true;
				} else if (obj instanceof IImportContainer) {
					return true;
				} else if (obj instanceof IJavaElement) {
					return true;
				} else if (obj instanceof JmlErrorElement) {
					return true;
				} else {
					// System.out.println("Unknown element type: " + obj + ". class: " + obj.getClass());

					// Things to look into further:
					// class org.eclipse.ui.internal.views.markers.MarkerEntry
					// class org.eclipse.ui.internal.views.log.LogEntry
					// let's see whether we can just use the worbench thing
					return enabledForFile(getWorkspaceFile(workbenchPart));
				}
			}
		}
		return false;
	}

	private static boolean enabledForFile(IFile file) {
		if( file==null ) return false;

		return JmlPlugin.isSupportedFileType(file.getName());
	}

	// keep consistent with enableForSelection
	private void addFiles() throws CoreException {
		if (selection == null || selection.isEmpty()
			|| selection instanceof ITextSelection) {
			// don't know what else to do...
			IFile res = getWorkspaceFile(workbenchPart);
			addFile(res);
		} else if (selection instanceof IStructuredSelection) {
			IStructuredSelection structured = (IStructuredSelection)selection;

			Iterator<?> iter = structured.iterator();
			while (iter.hasNext()) {
				Object obj = iter.next();

				if (obj instanceof IFile) {
					addFile((IFile)obj);
				} else if (obj instanceof IJavaProject) {
					addJavaProject((IJavaProject)obj);
				} else if (obj instanceof IPackageFragmentRoot) {
					addPackageFragmentRoot((IPackageFragmentRoot)obj);
				} else if (obj instanceof IPackageFragment) {
					addPackageFragment((IPackageFragment)obj);
				} else if (obj instanceof ICompilationUnit) {
					addCompilationUnit((ICompilationUnit)obj);
				} else if (obj instanceof IType) {
					IResource res = ((IType)obj).getUnderlyingResource();
					addResource(res);
				} else if (obj instanceof IPackageDeclaration) {
					IResource res = ((IPackageDeclaration)obj).getUnderlyingResource();
					addResource(res);
				} else if (obj instanceof IImportContainer) {
					IResource res = ((IImportContainer)obj).getUnderlyingResource();
					addResource(res);
				} else if (obj instanceof IJavaElement) {
					IResource res = ((IJavaElement)obj).getUnderlyingResource();
					addResource(res);
				} else if (obj instanceof JmlErrorElement) {
					addFile( ((JmlErrorElement) obj).getFile() );
				} else {
					IFile res = getWorkspaceFile(workbenchPart);
					addFile(res);
					// JmlPlugin.getDefault().getLog().log(new Status(IStatus.ERROR, JmlPlugin.PLUGIN_ID, "Unknown structured selection! Object: " + obj));
				}
			}
		} else {
			JmlPlugin.getDefault().getLog().log(new Status(IStatus.ERROR, JmlPlugin.PLUGIN_ID, "Do not know how to handle selection: " + selection));
		}
	}

	private static IFile getWorkspaceFile(IWorkbenchPart workbenchPart) {
		try {
			IEditorPart eP = workbenchPart.getSite().getWorkbenchWindow().getActivePage().getActiveEditor();
			IFileEditorInput input = (IFileEditorInput) eP.getEditorInput();
			return input.getFile();
		} catch( Throwable t ) {
			return null;
		}
	}

	private void addJavaProject(IJavaProject javaProject) throws CoreException
	{
		IPackageFragmentRoot[] packFragRoot =  javaProject.getAllPackageFragmentRoots();
		for (int i = 0; i < packFragRoot.length; ++i) 	{
			//System.out.println("PackageFragmentRoot=" + packFragRoot[i].getElementName());
			if (packFragRoot[i].getKind() == IPackageFragmentRoot.K_SOURCE) {
				addPackageFragmentRoot(packFragRoot[i]);
			}
		}
	}

	private void addPackageFragmentRoot(IPackageFragmentRoot packFragRoot) throws CoreException
	{
		IJavaElement[] elements = packFragRoot.getChildren();
		for (int i = 0; i < elements.length; ++i) {
			//System.out.println("Package=" + elements[i].getElementName());
			if (elements[i].getElementType() == IJavaElement.PACKAGE_FRAGMENT)
			{
				addPackageFragment((IPackageFragment)elements[i]);
			}
		}
	}

	private void addPackageFragment(IPackageFragment packFragment) throws CoreException
	{
		IJavaElement[] compUnits = packFragment.getChildren();
		for (int i = 0; i < compUnits.length; ++i)
		{
			//System.out.println("CompilationUnit=" + compUnits[i].getElementName());
			if (compUnits[i].getElementType() == IJavaElement.COMPILATION_UNIT) {
				addCompilationUnit((ICompilationUnit)compUnits[i]);
			}
		}
	}

	private void addCompilationUnit(ICompilationUnit compUnit) throws CoreException {
		IResource res = compUnit.getUnderlyingResource();
		if (res.getType() == IResource.FILE)
		{
			IFile file = (IFile)res;
			// System.out.println("Running file: " + file);
			addFile(file);
		}
	}

	private void addFile(IFile file) {
		if( JmlPlugin.isSupportedFileType(file.getName() )) {
			checkDirtyEditor(file);
			if( !cachedFiles.contains(file)) {
				cachedFiles.add(file);
			}
		}
	}

	private void addResource(IResource res) throws CoreException
	{
		if (res.getType() == IResource.FILE) {
			addFile((IFile)res);
		} else if (res.getType() == IResource.PROJECT) {
			IProject proj = (IProject)res;
			addJavaProject( JavaCore.create(proj) );
		}
	}


	private void checkDirtyEditor(final IFile file) {
        Display.getDefault().syncExec(new Runnable() {
            public void run() {
                IWorkbenchPage page = getCorrectPage();
                IEditorReference[] editors = page.getEditorReferences();
                for (int i = 0; i < editors.length; ++i) {
                    if (editors[i].getName() != null
                            && editors[i].getName().equals(file.getName())) {
                        if (editors[i].isDirty()) {
                            MessageBox mb = new MessageBox(page.getWorkbenchWindow().getShell(),
                                    SWT.YES | SWT.NO);
                            mb.setMessage("File " + file.getName()
                                            + " contains unsaved changes. Would you like to save?");
                            mb.setText("Save changes");
                            if (mb.open() == SWT.YES) {
                                editors[i].getEditor(true).doSave(null);
                            }
                        }
                    }
                }

            }
        });
	}

	/*
	private void showView(String id) {
		IWorkbenchPage page = getCorrectPage();
		try {
			page.showView(id);
		} catch (PartInitException e) {
			ErrorDialog.openError(getShell(), "Error", "Unable to open the "+ id + " view", new Status(IStatus.ERROR, JmlPlugin.PLUGIN_ID, 0,e.getMessage(),e));
		}
	} */

	private IWorkbenchPage getCorrectPage() {
		IWorkbenchPage page = null;
		if( workbenchPart != null ) {
			page = workbenchPart.getSite().getWorkbenchWindow().getActivePage();
		} else {
			JmlPlugin.getDefault().getLog().log(new Status(IStatus.ERROR, JmlPlugin.PLUGIN_ID, "Cannot determine correct workbench page!"));
		}
		return page;
	}
}
