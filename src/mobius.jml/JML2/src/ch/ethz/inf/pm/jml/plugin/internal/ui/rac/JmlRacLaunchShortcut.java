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

package ch.ethz.inf.pm.jml.plugin.internal.ui.rac;

import java.lang.reflect.InvocationTargetException;
import java.util.ArrayList;
import java.util.Collections;
import java.util.HashSet;
import java.util.List;
import java.util.Set;


import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IAdaptable;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.SubProgressMonitor;
import org.eclipse.debug.core.DebugPlugin;
import org.eclipse.debug.core.ILaunchConfiguration;
import org.eclipse.debug.core.ILaunchConfigurationType;
import org.eclipse.debug.core.ILaunchConfigurationWorkingCopy;
import org.eclipse.debug.core.ILaunchManager;
import org.eclipse.debug.ui.DebugUITools;
import org.eclipse.debug.ui.IDebugModelPresentation;
import org.eclipse.debug.ui.ILaunchShortcut;
import org.eclipse.jdt.core.IClassFile;
import org.eclipse.jdt.core.ICompilationUnit;
import org.eclipse.jdt.core.IJavaElement;
import org.eclipse.jdt.core.IMember;
import org.eclipse.jdt.core.IType;
import org.eclipse.jdt.core.JavaCore;
import org.eclipse.jdt.core.JavaModelException;
import org.eclipse.jdt.core.search.SearchEngine;
import org.eclipse.jdt.launching.IJavaLaunchConfigurationConstants;
import org.eclipse.jdt.ui.IJavaElementSearchConstants;
import org.eclipse.jdt.ui.JavaUI;
import org.eclipse.jface.dialogs.ErrorDialog;
import org.eclipse.jface.dialogs.MessageDialog;
import org.eclipse.jface.operation.IRunnableContext;
import org.eclipse.jface.operation.IRunnableWithProgress;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.jface.window.Window;
import org.eclipse.swt.widgets.Shell;
import org.eclipse.ui.IEditorInput;
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.IWorkbenchWindow;
import org.eclipse.ui.PlatformUI;
import org.eclipse.ui.dialogs.ElementListSelectionDialog;
import org.eclipse.ui.dialogs.SelectionDialog;

import ch.ethz.inf.pm.jml.plugin.internal.core.JmlPlugin;
import ch.ethz.inf.pm.jml.plugin.internal.core.JmlRacLaunchConfigurationDelegate;

/**
 * @author Paolo Bazzi
 * 
 */

public class JmlRacLaunchShortcut implements ILaunchShortcut {

	private ILaunchConfiguration createConfiguration(IType type) {
		ILaunchConfiguration config = null;
		try {
			ILaunchConfigurationType configType = getConfigurationType();
			ILaunchConfigurationWorkingCopy wc = configType.newInstance(null, DebugPlugin.getDefault().getLaunchManager().generateUniqueLaunchConfigurationNameFrom(type.getElementName())); 
			wc.setAttribute(IJavaLaunchConfigurationConstants.ATTR_MAIN_TYPE_NAME, type.getFullyQualifiedName());
			wc.setAttribute(IJavaLaunchConfigurationConstants.ATTR_PROJECT_NAME, type.getJavaProject().getElementName());
			wc.setMappedResources(new IResource[] {type.getJavaProject().getProject()});
			config = wc.doSave();		
		} catch (CoreException ce) {
			ErrorDialog.openError(getShell(), "Error", ce.getMessage(), ce.getStatus());
		}
		return config;
	}

	private ILaunchConfigurationType getConfigurationType() {
		ILaunchManager lm= DebugPlugin.getDefault().getLaunchManager();
		return lm.getLaunchConfigurationType(JmlRacLaunchConfigurationDelegate.JML_RAC_CONFIGURATION_TYPE);		
	}

	/**
	 * @see ILaunchShortcut#launch(ISelection, String)
	 */
	public void launch(ISelection selection, String mode) {
		if (selection instanceof IStructuredSelection) {
			searchAndLaunch(((IStructuredSelection)selection).toArray(), mode, "Please select a type", "No main type found.");
		}
	}

	/**
	 * @see ILaunchShortcut#launch(IEditorPart, String)
	 */
	public void launch(IEditorPart editor, String mode) {
		IEditorInput input = editor.getEditorInput();
		IJavaElement je = (IJavaElement) input.getAdapter(IJavaElement.class);
		if (je != null) {
			searchAndLaunch(new Object[] {je}, mode, "Please select a type", "No main type found.");
		}
	}	
	
	/**
	 * Launches a configuration for the given type
	 */
	private void launch(IType type, String mode) {
		ILaunchConfiguration config = findLaunchConfiguration(type, getConfigurationType());
		if (config != null) {
			DebugUITools.launch(config, mode);
		}			
	}
	
	/**
	 * Searches main types and launch the selected one
	 * 
	 * @param search the java elements to search for a main type
	 * @param mode the mode to launch in
	 * @param selectMessage message for the type selection dialog
	 * @param emptyMessage message if selection or editor selection was empty	 * 
	 */
	public void searchAndLaunch(Object[] search, String mode, String selectMessage, String emptyMessage) {
		IType[] types = null;
		try {
			types = findTypes(search, PlatformUI.getWorkbench().getProgressService());
		} catch (InterruptedException e) {
			return;
		}		
		IType type = null;
		if (types.length == 0) {
			MessageDialog.openError(getShell(), "Error launching", emptyMessage); 
		} else if (types.length > 1) {
			try {
				type = chooseType(types, selectMessage);
			} catch (JavaModelException e) {
				ErrorDialog.openError(getShell(),"Error",e.getMessage(),e.getStatus());
				return;
			}
		} else {
			type = types[0];
		}
		if (type != null) {
			launch(type, mode);
		} 
	}	
	
		
	/**
	 * Finds and returns the launchable types in the given selection of elements.
	 * 
	 * @param elements scope to search for launchable types
	 * @param context progess reporting context
	 * @return launchable types, possibly empty
	 * @exception InterruptedException if the search is cancelled
	 * @exception org.eclipse.core.runtime.CoreException if the search fails
	 */
	private static IType[] findTypes(final Object[] elements, IRunnableContext context) throws InterruptedException { 
		final Set<Object> result= new HashSet<Object>();
		try {
			if (elements.length > 0) {
				IRunnableWithProgress runnable= new IRunnableWithProgress() {
					public void run(IProgressMonitor pm) throws InterruptedException {
						int nElements= elements.length;
						pm.beginTask("Searching types", nElements); 
						try {
							for (int i= 0; i < nElements; i++) {
								try {
									collectTypes(elements[i], new SubProgressMonitor(pm, 1), result);
								} catch (JavaModelException jme) { 
									JmlPlugin.getDefault().getLog().log(jme.getStatus());
								}
								if (pm.isCanceled()) {
									throw new InterruptedException();
								}
							}
						} finally {
							pm.done();
						}
					}
				};
				context.run(true, true, runnable);			
			}
			return result.toArray(new IType[result.size()]) ;
		} catch (InvocationTargetException e) {
			return null;
		}		
	}
	
	public static void collectTypes(Object element, IProgressMonitor monitor, Set<Object> result) throws JavaModelException/*, InvocationTargetException*/ {
		element = computeScope(element);

		// iterate upwards if a method,field or initializer is selected
		while(element instanceof IMember) {
			if(element instanceof IType) {
				result.add(element);
				monitor.done();
				return;
			}
			element= ((IJavaElement)element).getParent();
		}
		// compilation unit selected
		if (element instanceof ICompilationUnit) {
			ICompilationUnit cu= (ICompilationUnit)element;
			IType[] types= cu.getAllTypes();
			for (int i= 0; i < types.length; i++) {
				result.add(types[i]);
			}
		} 
		// class file selected (eg. in navigator view) 
		else if (element instanceof IClassFile) {
			IType type = ((IClassFile)element).getType();
			result.add(type);
		} 
		// java model, java project, package root, package selected  
		else if (element instanceof IJavaElement) {
			// TODO search for types in project,packages ect. 
		}
		monitor.done();
	}
	
	private static Object computeScope(Object element) {
        // determine IJavaElement if a file ressource is selected	
		if (element instanceof IJavaElement) {
            return element;
        }
		// adaptable to a ressource
		if (element instanceof IAdaptable) {
			element = ((IAdaptable)element).getAdapter(IResource.class);
		}
		// create java element out of resource  eg. class file
		if (element instanceof IResource) {
			IJavaElement javaElement = JavaCore.create((IResource)element);
			element = javaElement;
		}
		return element;
	}

	
	/**
	 * Prompts the user to select a type from the given types.
	 * 
	 * @param types the types to choose from
	 * @param title the selection dialog title
	 * 
	 * @return the selected type or <code>null</code> if none.
	 */
	protected IType chooseType(IType[] types, String title) throws JavaModelException {
		SelectionDialog dialog = JavaUI.createTypeDialog(
				getShell(),
				PlatformUI.getWorkbench().getProgressService(), 
				SearchEngine.createJavaSearchScope(types), 
				IJavaElementSearchConstants.CONSIDER_CLASSES, false, "**"); //$NON-NLS-1$
		dialog.setMessage("Choose main type to launch");
		dialog.setTitle(title);
		if (dialog.open() == Window.OK) {
			return (IType)dialog.getResult()[0];
		}
		return null;
	}

	/**
	 * Locate a configuration to relaunch for the given type.  If one cannot be found, create one.
	 * 
	 * @return a re-useable config or <code>null</code> if none
	 */
	protected ILaunchConfiguration findLaunchConfiguration(IType type, ILaunchConfigurationType configType) {
		List<ILaunchConfiguration> candidateConfigs = Collections.emptyList();
		try {
			ILaunchConfiguration[] configs = DebugPlugin.getDefault().getLaunchManager().getLaunchConfigurations(configType);
			candidateConfigs = new ArrayList<ILaunchConfiguration>(configs.length);
			for (int i = 0; i < configs.length; i++) {
				ILaunchConfiguration config = configs[i];
				if (config.getAttribute(IJavaLaunchConfigurationConstants.ATTR_MAIN_TYPE_NAME, "").equals(type.getFullyQualifiedName())) { //$NON-NLS-1$
					if (config.getAttribute(IJavaLaunchConfigurationConstants.ATTR_PROJECT_NAME, "").equals(type.getJavaProject().getElementName())) { //$NON-NLS-1$
						candidateConfigs.add(config);
					}
				}
			}
		} catch (CoreException e) {
			ErrorDialog.openError(getShell(), "Error", e.getMessage(), e.getStatus());
		}
		
		// If there are no existing configs associated with the IType, create one.
		// If there is exactly one config associated with the IType, return it.
		// Otherwise, if there is more than one config associated with the IType, prompt the 
		// user to choose one.
		int candidateCount = candidateConfigs.size();
		if (candidateCount < 1) {
			return createConfiguration(type);
		} else if (candidateCount == 1) {
			return candidateConfigs.get(0);
		} else {
			// Prompt the user to choose a config.  A null result means the user
			// cancelled the dialog, in which case this method returns null,
			// since cancelling the dialog should also cancel launching anything.
			ILaunchConfiguration config = chooseConfiguration(candidateConfigs);
			if (config != null) {
				return config;
			}
		}		
		return null;
	}
	
	/**
	 * Show a selection dialog that allows the user to choose one of the specified
	 * launch configurations.  Return the chosen config, or <code>null</code> if the
	 * user cancelled the dialog.
	 */
	protected ILaunchConfiguration chooseConfiguration(List<ILaunchConfiguration> configList) {
		IDebugModelPresentation labelProvider = DebugUITools.newDebugModelPresentation();
		ElementListSelectionDialog dialog= new ElementListSelectionDialog(getShell(), labelProvider);
		dialog.setElements(configList.toArray());
		dialog.setTitle("Select configuration");   
		dialog.setMessage("Please select a launch configuration");
		dialog.setMultipleSelection(false);
		int result = dialog.open();
		labelProvider.dispose();
		if (result == Window.OK) {
			return (ILaunchConfiguration) dialog.getFirstResult();
		}
		return null;		
	}
	
	/**
	 * Convenience method to get the window that owns this action's Shell.
	 */
	protected Shell getShell() {
		IWorkbenchWindow window = PlatformUI.getWorkbench().getActiveWorkbenchWindow();
		if (window != null) {
			return window.getShell();
		}
		return null;
	}
}
