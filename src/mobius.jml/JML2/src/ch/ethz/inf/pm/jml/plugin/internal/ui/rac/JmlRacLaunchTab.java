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


import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.debug.core.ILaunchConfiguration;
import org.eclipse.debug.core.ILaunchConfigurationWorkingCopy;
import org.eclipse.jdt.debug.ui.launchConfigurations.JavaLaunchTab;
import org.eclipse.jdt.launching.IJavaLaunchConfigurationConstants;
import org.eclipse.jface.dialogs.ErrorDialog;
import org.eclipse.swt.SWT;
import org.eclipse.swt.events.ModifyEvent;
import org.eclipse.swt.events.ModifyListener;
import org.eclipse.swt.events.SelectionEvent;
import org.eclipse.swt.events.SelectionListener;
import org.eclipse.swt.graphics.Font;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Button;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Group;

import ch.ethz.inf.pm.jml.plugin.internal.core.JmlRacLaunchConfigurationDelegate;
import ch.ethz.inf.pm.jml.plugin.internal.core.properties.JmlPropertiesProvider;
import ch.ethz.inf.pm.jml.plugin.internal.core.properties.JmlRacProperties;
import ch.ethz.inf.pm.jml.plugin.resources.ResourceConstants;

/**
 * @author Paolo Bazzi
 *
 */

public class JmlRacLaunchTab extends JavaLaunchTab {

	/**
	 * A listener which handles widget change events for the controls
	 * in this tab.
	 */
	private class WidgetListener implements ModifyListener, SelectionListener {
		public void modifyText(ModifyEvent e) {
			updateLaunchConfigurationDialog();
		}
		public void widgetDefaultSelected(SelectionEvent e) {/*do nothing*/}

		public void widgetSelected(SelectionEvent e) {
			updateLaunchConfigurationDialog();
		}
	}//end private class

	private Button fAutoBuild;

	private final WidgetListener fListener = new WidgetListener();

	public void createControl(Composite parent) {
		Font font = parent.getFont();
		Composite comp = new Composite(parent, SWT.NONE);
		setControl(comp);

		GridLayout topLayout = new GridLayout();
		topLayout.verticalSpacing = 0;
		comp.setLayout(topLayout);
		comp.setFont(font);

		Group group= new Group(comp, SWT.NONE);
		group.setText("JML2 Runtime Assertion Checker");
		GridData gd = new GridData(GridData.FILL_HORIZONTAL);
		group.setLayoutData(gd);
		GridLayout layout = new GridLayout();
		layout.numColumns = 2;
		group.setLayout(layout);
		group.setFont(font);

		fAutoBuild = new Button(group, SWT.CHECK);
		fAutoBuild.setText("Always build project and its dependencies before launch");
		fAutoBuild.addSelectionListener(fListener);
	}

	public String getName() {
		return "JML2 RAC";
	}

	public void performApply(ILaunchConfigurationWorkingCopy config) {
		config.setAttribute(JmlRacLaunchConfigurationDelegate.ATTR_AUTO_BUILD, fAutoBuild.getSelection());
	}

	public void setDefaults(ILaunchConfigurationWorkingCopy config) {
		IProject project = getProject(config);
		if (project != null)
		{
			JmlPropertiesProvider props = JmlPropertiesProvider.getPropertiesProvider(ResourceConstants.RAC_DEF_PROPERTIES_FILE);
			try {
				config.setAttribute(JmlRacLaunchConfigurationDelegate.ATTR_AUTO_BUILD, props.getBooleanProperty(JmlRacProperties.AUTO_BUILD, project));
			} catch (CoreException e) {
				ErrorDialog.openError(getShell(), "Error", e.getMessage(), e.getStatus());
			}
		}
	}

	private void updateFromConfig(ILaunchConfiguration config) {
		try {
			IProject project = getProject(config);
			JmlPropertiesProvider props = JmlPropertiesProvider.getPropertiesProvider(ResourceConstants.RAC_DEF_PROPERTIES_FILE);
			boolean autoBuild = config.getAttribute(JmlRacLaunchConfigurationDelegate.ATTR_AUTO_BUILD, props.getBooleanProperty(JmlRacProperties.AUTO_BUILD, project));
			fAutoBuild.setSelection(autoBuild);
		} catch (CoreException e) {
			ErrorDialog.openError(getShell(), "Error", "Error getting project properties from configuration.", e.getStatus());
		}
	}

	/* (non-Javadoc)
	 * @see org.eclipse.debug.ui.ILaunchConfigurationTab#initializeFrom(org.eclipse.debug.core.ILaunchConfiguration)
	 */
	@Override
	public void initializeFrom(ILaunchConfiguration config) {
		updateFromConfig(config);
		super.initializeFrom(config);
	}

	private IProject getProject(ILaunchConfiguration configuration) {
		String projectName = null;
		try {
			projectName = configuration.getAttribute(IJavaLaunchConfigurationConstants.ATTR_PROJECT_NAME,(String) null);
		} catch (CoreException e) {
			ErrorDialog.openError(getShell(), "Error", "Error getting project name from configuration.", e.getStatus());
		}
		if (projectName != null) {
			projectName = projectName.trim();
			if (projectName.length() > 0) {
				IProject project = ResourcesPlugin.getWorkspace().getRoot().getProject(projectName);
				if (project.exists())
				{
					return project;
				}
			}
		}
		return null;
	}
}
