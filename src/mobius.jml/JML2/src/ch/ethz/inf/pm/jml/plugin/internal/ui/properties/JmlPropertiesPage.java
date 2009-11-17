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
import org.eclipse.core.runtime.IAdaptable;
import org.eclipse.jdt.core.IJavaElement;
import org.eclipse.jdt.core.IJavaProject;
import org.eclipse.jface.dialogs.Dialog;
import org.eclipse.jface.preference.PreferencePage;
import org.eclipse.swt.SWT;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Control;
import org.eclipse.swt.widgets.Label;
import org.eclipse.ui.dialogs.PropertyPage;

/**
 * @author Paolo Bazzi
 *
 */
public abstract class JmlPropertiesPage extends PropertyPage {
	protected static final int TEXT_FIELD_SMALL_WIDTH = 10;
	protected static final int TEXT_FIELD_WIDE_WIDTH = 70;
	protected static final int COMBO_WIDTH = 15;

	/**
	 * @see PreferencePage#createContents(Composite)
	 */
	@Override
	protected Control createContents(Composite parent) {
		Composite composite= new Composite(parent, SWT.NONE);
		GridLayout layout= new GridLayout();
		layout.marginHeight= 0;
		layout.marginWidth= 0;
		composite.setLayout(layout);
		composite.setFont(parent.getFont());

		GridData data= new GridData(GridData.FILL, GridData.FILL, true, true);

		Control fPropertiesBlockControl= createPreferenceContent(composite);
		fPropertiesBlockControl.setLayoutData(data);

		Dialog.applyDialogFont(composite);
		return composite;
	}

	protected abstract Control createPreferenceContent(Composite composite);

	protected void addSeparator(Composite parent) {
		Label separator = new Label(parent, SWT.SEPARATOR | SWT.HORIZONTAL);
		GridData gridData = new GridData();
		gridData.horizontalAlignment = GridData.FILL;
		gridData.grabExcessHorizontalSpace = true;
		separator.setLayoutData(gridData);
	}

	protected ScrolledPropPageContent getParentScrolledComposite(Control control) {
		Control parent= control.getParent();
		while (!(parent instanceof ScrolledPropPageContent)) {
			parent= parent.getParent();
		}
		// if (parent instanceof ScrolledPropPageContent) {
		// the above is is not needed, the loop only ends when parent
		// is either null or an instanceof SPPC.
		return (ScrolledPropPageContent) parent;
	}


	protected Composite createDefaultComposite(Composite parent) {
		Composite composite = new Composite(parent, SWT.NULL);
		GridLayout layout = new GridLayout();
		layout.numColumns = 2;

		composite.setLayout(layout);

		GridData data = new GridData();
		data.verticalAlignment = GridData.FILL;
		data.horizontalAlignment = GridData.FILL;
		data.grabExcessHorizontalSpace = true;

		composite.setLayoutData(data);
		return composite;
	}

	protected IProject getProject() {
		IAdaptable adaptable= getElement();
		if (adaptable != null) {
			IJavaElement elem= (IJavaElement) adaptable.getAdapter(IJavaElement.class);
			if (elem instanceof IJavaProject) {
				return ((IJavaProject) elem).getProject();
			}
		}
		return null;
	}
}

//protected Combo addComboBox(Composite parent, String label, /*Key key,*/ String[] values, String[] valueLabels, int indent) {
//GridData gd= new GridData(GridData.FILL, GridData.CENTER, true, false, 2, 1);
//gd.horizontalIndent= indent;
//
//Label labelControl= new Label(parent, SWT.LEFT);
//labelControl.setFont(JFaceResources.getDialogFont());
//labelControl.setText(label);
//labelControl.setLayoutData(gd);
//
//Combo comboBox= newComboControl(parent,/* key,*/ values, valueLabels);
//comboBox.setLayoutData(new GridData(GridData.HORIZONTAL_ALIGN_FILL));
//
//fLabels.put(comboBox, labelControl);
//
//return comboBox;
//}
//protected Combo newComboControl(Composite composite, Key key, String[] values, String[] valueLabels) {
//ControlData data= new ControlData(key, values);
//
//Combo comboBox= new Combo(composite, SWT.READ_ONLY);
//comboBox.setItems(valueLabels);
//comboBox.setData(data);
//comboBox.addSelectionListener(getSelectionListener());
//comboBox.setFont(JFaceResources.getDialogFont());
//
//makeScrollableCompositeAware(comboBox);
//
//String currValue= getValue(key);
//comboBox.select(data.getSelection(currValue));
//
//fComboBoxes.add(comboBox);
//return comboBox;
//}
//private void makeScrollableCompositeAware(Control control) {
//ScrolledPropPageContent parentScrolledComposite= getParentScrolledComposite(control);
//if (parentScrolledComposite != null) {
//	parentScrolledComposite.adaptChild(control);
//}
//}

//protected Button addCheckBox(Composite parent, String label, /*Key key,*/ String[] values, int indent) {
////ControlData data= new ControlData(key, values);
//
//GridData gd= new GridData(GridData.HORIZONTAL_ALIGN_FILL);
//gd.horizontalSpan= 3;
//gd.horizontalIndent= indent;
//
//Button checkBox= new Button(parent, SWT.CHECK);
//checkBox.setFont(JFaceResources.getDialogFont());
//checkBox.setText(label);
////checkBox.setData(data);
//checkBox.setLayoutData(gd);
////checkBox.addSelectionListener(getSelectionListener());
//
//makeScrollableCompositeAware(checkBox);
//
////String currValue= getValue(key);
////checkBox.setSelection(data.getSelection(currValue) == 0);
//
//fCheckBoxes.add(checkBox);
//
//return checkBox;
//}
