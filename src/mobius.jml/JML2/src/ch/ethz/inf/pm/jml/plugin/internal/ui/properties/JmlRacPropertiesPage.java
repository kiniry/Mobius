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


import org.eclipse.core.resources.IProject;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.QualifiedName;
import org.eclipse.core.runtime.Status;
import org.eclipse.jface.dialogs.ErrorDialog;
import org.eclipse.swt.SWT;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Button;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Control;

import ch.ethz.inf.pm.jml.plugin.internal.core.JmlPlugin;
import ch.ethz.inf.pm.jml.plugin.internal.core.properties.JmlPropertiesProvider;
import ch.ethz.inf.pm.jml.plugin.internal.core.properties.JmlRacProperties;
import ch.ethz.inf.pm.jml.plugin.resources.ResourceConstants;

/**
 * @author Paolo Bazzi
 *
 */
public class JmlRacPropertiesPage  extends JmlPropertiesPage {
	private Button autoBuild;
	private Composite fControlsComposite;

	@Override
	protected Control createPreferenceContent(Composite comp) {
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

		Composite composite2 = createDefaultComposite(fControlsComposite);
		IProject project = getProject();
		JmlPropertiesProvider checkerProps = JmlPropertiesProvider.getPropertiesProvider(ResourceConstants.RAC_DEF_PROPERTIES_FILE);

		GridLayout gridLayout = new GridLayout();
	    gridLayout.numColumns = 1;
		composite.setLayout(gridLayout);
		try {
			autoBuild = new Button(composite2,SWT.CHECK);
			autoBuild.setText("Always build project and its dependencies before launch");
			autoBuild.setSelection(checkerProps.getBooleanProperty(JmlRacProperties.AUTO_BUILD,project));
		} catch (CoreException e) {
			ErrorDialog.openError(getShell(), "Error", e.getMessage(), e.getStatus());
		}
		return sc1;
	}

	@Override
	protected void performDefaults() {
		JmlPropertiesProvider checkerProps = JmlPropertiesProvider.getPropertiesProvider(ResourceConstants.RAC_DEF_PROPERTIES_FILE);
		try {
			autoBuild.setSelection(checkerProps.getBooleanDefaultProperty(JmlRacProperties.AUTO_BUILD));
		} catch (CoreException e) {
			ErrorDialog.openError(getShell(), "Error", e.getMessage(), e.getStatus());
		}
	}

	@Override
	public boolean performOk() {
		IProject p = getProject();
		try {
			p.setPersistentProperty(new QualifiedName(JmlPlugin.PLUGIN_ID,JmlRacProperties.AUTO_BUILD), String.valueOf(autoBuild.getSelection()));
		} catch (CoreException e) {
	          JmlPlugin.getDefault().getLog().log(
	                    new Status(IStatus.ERROR, JmlPlugin.PLUGIN_ID, e.getMessage(), e));
			return false;
		}
		return true;
	}
}
