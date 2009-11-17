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

package ch.ethz.inf.pm.jml.plugin.internal.ui.properties;

import java.util.Dictionary;

import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IProjectDescription;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Platform;
import org.eclipse.core.runtime.QualifiedName;
import org.eclipse.core.runtime.Status;
import org.eclipse.jface.dialogs.ErrorDialog;
import org.eclipse.swt.SWT;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Button;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Control;
import org.eclipse.swt.widgets.Label;
import org.jmlspecs.checker.JmlVersionOptions;
import org.osgi.framework.Bundle;

import ch.ethz.inf.pm.jml.plugin.internal.core.JmlPlugin;
import ch.ethz.inf.pm.jml.plugin.internal.core.builder.JmlCheckerNature;
import ch.ethz.inf.pm.jml.plugin.internal.core.properties.JmlPluginProperties;
import ch.ethz.inf.pm.jml.plugin.internal.core.properties.JmlPropertiesProvider;
import ch.ethz.inf.pm.jml.plugin.resources.MultiJavaVersionDummy;
import ch.ethz.inf.pm.jml.plugin.resources.ResourceConstants;

/**
 * @author Paolo Bazzi
 *
 */

public class JmlRootPropertiesPage extends JmlPropertiesPage {
	private final static String BUNDLE_NAME = "Bundle-Name";
	private final static String BUNDLE_VERSION = "Bundle-Version";

	private Composite fControlsComposite;

	private Button statusMessages;
	private Button autoCheck;

	@SuppressWarnings("unchecked")
	@Override
	protected Control createPreferenceContent(Composite comp) {
		IProject project = getProject();
		JmlPropertiesProvider topProps = JmlPropertiesProvider.getPropertiesProvider(ResourceConstants.PLUGIN_DEF_PROPERTIES_FILE);


		final ScrolledPropPageContent sc1 = new ScrolledPropPageContent(comp);
		Composite composite= sc1.getBody();
		GridLayout layout= new GridLayout();
		layout.marginHeight= 0;
		layout.marginWidth= 0;
		composite.setLayout(layout);

		fControlsComposite= new Composite(composite, SWT.NONE);
		fControlsComposite.setFont(composite.getFont());
		fControlsComposite.setLayoutData(new GridData(GridData.FILL, GridData.FILL, true, false));
		layout= new GridLayout();
		layout.marginHeight= 0;
		layout.marginWidth= 0;
		layout.numColumns= 1;
		fControlsComposite.setLayout(layout);

		// JML2 Plugin version
		Bundle bundle = Platform.getBundle(JmlPlugin.PLUGIN_ID);
		Dictionary<String, String> dic = bundle.getHeaders();
		String name = dic.get(BUNDLE_NAME);
		String ver = dic.get(BUNDLE_VERSION);
		Label jmlPlugin = new Label(composite,SWT.NONE);
		jmlPlugin.setText(name + " version: " + ver);

		// JML2 Resources Plugin Version
		bundle = Platform.getBundle(ResourceConstants.JML_RESOURCES_PLUGIN_NAME);
		dic = bundle.getHeaders();
		name = dic.get(BUNDLE_NAME);
		ver = dic.get(BUNDLE_VERSION);
		Label jmlResPlugin = new Label(composite,SWT.NONE);
		jmlResPlugin.setText(name + " version: " + ver);

		Label space = new Label(composite,SWT.NONE);
		space.setText("");

		// Multijava tools version
		Label mj = new Label(composite,SWT.NONE);
		MultiJavaVersionDummy mjOpt  = new MultiJavaVersionDummy();
		mj.setText("Multijava tools: \"" + mjOpt.getVersion() +"\"");

		// JML2 Tools version
		Label jml = new Label(composite,SWT.NONE);
		JmlVersionOptions jmlOpt = new JmlVersionOptions();
		String jmlVer = jmlOpt.version();
		// WMD: removed this... 15.11.2007
		// if (jmlVer.length() > 18) { jmlVer = jmlVer.substring(18,jmlVer.length()); }
		jml.setText("JML2 tools: \"" + jmlVer +"\"");

		space = new Label(composite,SWT.NONE);
		space.setText("");
		addSeparator(composite);
		space = new Label(composite,SWT.NONE);
		space.setText("");

		try {
			// Whether to output status messages
			statusMessages = new Button(composite,SWT.CHECK);
			statusMessages.setText("Show status messages");
			statusMessages.setSelection(topProps.getBooleanProperty(JmlPluginProperties.STATUS_MESSAGES, project));


			// Toggle auto-build
			autoCheck = new Button(composite,SWT.CHECK);
			autoCheck.setText("Automatically run JML2 Checker");
			autoCheck.setSelection(topProps.getBooleanProperty(JmlPluginProperties.AUTO_CHECK, project));
		} catch (CoreException e) {
			ErrorDialog.openError(getShell(), "Error", e.getMessage(), e.getStatus());
		}

		return sc1;
	}


	@Override
	protected void performDefaults() {
		JmlPropertiesProvider topProps = JmlPropertiesProvider.getPropertiesProvider(ResourceConstants.PLUGIN_DEF_PROPERTIES_FILE);
		try {
			statusMessages.setSelection(topProps.getBooleanDefaultProperty(JmlPluginProperties.STATUS_MESSAGES));
			autoCheck.setSelection(topProps.getBooleanDefaultProperty(JmlPluginProperties.AUTO_CHECK));
		} catch (CoreException e) {
			ErrorDialog.openError(getShell(), "Error", e.getMessage(), e.getStatus());
		}
	}

	@Override
	public boolean performOk() {
		IProject p = getProject();
		try {
			p.setPersistentProperty(new QualifiedName(JmlPlugin.PLUGIN_ID, JmlPluginProperties.STATUS_MESSAGES), String.valueOf(statusMessages.getSelection()));
			p.setPersistentProperty(new QualifiedName(JmlPlugin.PLUGIN_ID, JmlPluginProperties.AUTO_CHECK), String.valueOf(autoCheck.getSelection()));

			setNature(p, autoCheck.getSelection());
		} catch (CoreException e) {
	        JmlPlugin.getDefault().getLog().log(
	                    new Status(IStatus.ERROR, JmlPlugin.PLUGIN_ID, e.getMessage(), e));
			return false;
		}
		return true;
	}


	private void setNature(IProject project, boolean toCheck) {
		try {
			IProjectDescription description = project.getDescription();
			String[] natures = description.getNatureIds();

			for (int i = 0; i < natures.length; ++i) {
				if (JmlCheckerNature.NATURE_ID.equals(natures[i])) {
					// the project already has the nature
					if (!toCheck) {
						// remove the nature
						String[] newNatures = new String[natures.length - 1];
						System.arraycopy(natures, 0, newNatures, 0, i);
						System.arraycopy(natures, i + 1, newNatures, i,
								natures.length - i - 1);
						description.setNatureIds(newNatures);
						project.setDescription(description, null);
					}

					return;
				}
			}

			if (toCheck) {
				// we come here if the project does not already contain
				// the nature and we should add the nature
				String[] newNatures = new String[natures.length + 1];
				System.arraycopy(natures, 0, newNatures, 0, natures.length);
				newNatures[natures.length] = JmlCheckerNature.NATURE_ID;
				description.setNatureIds(newNatures);
				project.setDescription(description, null);
			}
		} catch (CoreException e) {
			JmlPlugin.getDefault().getLog().log( new Status(IStatus.WARNING, JmlPlugin.PLUGIN_ID,
					"A problem occured when switching the JML2 project nature: " + e ));
		}
	}
}
