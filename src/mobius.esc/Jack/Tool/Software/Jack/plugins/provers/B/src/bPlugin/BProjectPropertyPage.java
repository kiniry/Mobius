//******************************************************************************
/* Copyright (c) 2002, 2003 GEMPLUS Software Research Labs. All Rights Reserved.
/* Copyright (c) 2003, 2004 INRIA. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: JackProjectPropertyPage.java
/*
/********************************************************************************
/* Warnings/Remarks:
/*******************************************************************************/
package bPlugin;

import jab.eJab;
import jack.plugin.JackPlugin;
import jack.util.Logger;

import java.net.MalformedURLException;
import java.rmi.NotBoundException;
import java.rmi.RemoteException;

import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.jdt.core.IJavaProject;
import org.eclipse.jface.dialogs.Dialog;
import org.eclipse.jface.dialogs.IInputValidator;
import org.eclipse.jface.dialogs.InputDialog;
import org.eclipse.jface.dialogs.MessageDialog;
import org.eclipse.swt.SWT;
import org.eclipse.swt.events.SelectionEvent;
import org.eclipse.swt.events.SelectionListener;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.layout.RowLayout;
import org.eclipse.swt.widgets.Button;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Control;
import org.eclipse.swt.widgets.Label;
import org.eclipse.swt.widgets.List;
import org.eclipse.swt.widgets.Shell;
import org.eclipse.ui.dialogs.PropertyPage;

/**
 * Property page for Java projects.
 * <p>
 * 
 * @author A. Requet
 */
public class BProjectPropertyPage extends PropertyPage {

	private Label editedProject;
	private String getABProject() {
		IJavaProject project = (IJavaProject) getElement();
		IResource resource = project.getResource();

		try {
			return resource.getPersistentProperty(BPlugin.AB_PROJECT_PROPERTY);
		} catch (CoreException e) {
			Logger.err.println("Exception catched: " + e.toString());
			return null;
		}

	}

	/**
	 * Set the property associated to the AtelierB project.
	 * 
	 * @return true in case of success, false otherwise.
	 */
	boolean setABProject(String new_value)
		throws RemoteException, MalformedURLException, NotBoundException {
		eJab ab = AbServer.abconnect(getClass());
		if (ab != null)
			try {
				if (ab.checkProject(new_value)) {

					IJavaProject project = (IJavaProject) getElement();
					IResource resource = project.getResource();
					try {
						resource.setPersistentProperty(
							BPlugin.AB_PROJECT_PROPERTY,
							new_value);
					} catch (CoreException e) {
						Logger.err.println(
							"Exception catched: " + e.toString());
						return false;
					}
					return true;
				}
			} catch (java.rmi.RemoteException re) {
				Logger.err.println(re.getMessage());
			}
		return false;
	}

	/**
	 * @see PreferencePage#createContents(Composite)
	 */
	protected Control createContents(Composite parent) {
		Composite composite = new Composite(parent, SWT.NONE);
		GridLayout layout = new GridLayout();
		layout.numColumns = 3;

		composite.setLayout(layout);
		GridData data;

		//Label for project field
		Label project_label = new Label(composite, SWT.NONE);
		project_label.setText("Atelier B project :");

		data = new GridData(GridData.FILL);
		project_label.setLayoutData(data);

		editedProject = new Label(composite, SWT.NONE);
		data = new GridData(GridData.FILL);
		data.grabExcessHorizontalSpace = true;

		editedProject.setLayoutData(data);

		String project_string = getABProject();
		if (project_string != null)
			editedProject.setText(project_string);

		// the button allowing to change the project
		Button button = new Button(composite, SWT.PUSH);
		button.setText("Change project");
		button.addSelectionListener(new SelectionListener() {
			public void widgetDefaultSelected(SelectionEvent e) {
			}
			public void widgetSelected(SelectionEvent e) {
				try {
					ProjectSelectionDialog dlg =
						new ProjectSelectionDialog(getShell());
					if (dlg.open() == org.eclipse.jface.window.Window.OK)
						setABProject(dlg.getSelectedProject());
					editedProject.setText(dlg.getSelectedProject());
					editedProject.redraw();
				} catch (Exception re) {
					AbServer.remoteExceptionDialog(
						getShell(),
						"jack.plugin",
						"Wrong Atelier B connection",
						re);
				}
			}
		});
		data = new GridData(GridData.FILL);
		button.setLayoutData(data);

		return composite;
	}

	/**
	 * Resets the settings to the default ones.
	 */
	protected void performDefaults() {
		// Populate the owner text field with the default value
		editedProject.setText("Undefined Project");
	}

	/**
	 * Applies the changes performed in the dialog.
	 */
	public boolean performOk() {
		try {
			setABProject(editedProject.getText());
		} catch (Exception re) {
			AbServer.remoteExceptionDialog(
				getShell(),
				JackPlugin.DIALOG_TITLE,
				"Error setting properties",
				re);
			return false;
		}
		return true;
	}

}

class ProjectSelectionDialog extends Dialog {

	ProjectSelectionDialog(Shell s)
		throws RemoteException, MalformedURLException, NotBoundException {
		super(s);

		ab = AbServer.abconnect(getClass());
		try {
			if (ab != null)
				ab.initialize(true);
		} catch (java.rmi.RemoteException re) {
		}
	}

	eJab ab;
	List list;
	Button removeButton;
	String selectedProject;

	void setProjectList() {
		list.removeAll();
		String[] projectList = {
		};
		if (ab != null)
			try {
				projectList = ab.getProjectList();
			} catch (java.rmi.RemoteException re) {
			}
		for (int i = 0; i < projectList.length; i++)
			list.add(projectList[i]);
	}

	void newProject(String project) {
		if (ab != null)
			try {
				ab.newProject(project);
			} catch (java.rmi.RemoteException re) {
			}
		setProjectList();
		list.select(list.indexOf(project));
	}

	void removeProject(String project) {
		if (ab != null)
			try {
				ab.removeProject(project);
			} catch (java.rmi.RemoteException re) {
			}
		setProjectList();
		removeButton.setEnabled(false);
	}

	protected Control createDialogArea(Composite parent) {
		Composite composite = (Composite) super.createDialogArea(parent);
		//add controls to composite

		GridLayout layout = new GridLayout();
		layout.numColumns = 2;
		composite.setLayout(layout);

		list = new List(composite, SWT.SINGLE | SWT.BORDER);
		list.addSelectionListener(new SelectionListener() {
			public void widgetDefaultSelected(SelectionEvent e) {
			}
			public void widgetSelected(SelectionEvent e) {
				removeButton.setEnabled(true);
			}
		});

		setProjectList();

		GridData gdata1 = new GridData(GridData.FILL);
		gdata1.grabExcessHorizontalSpace = true;
		gdata1.grabExcessVerticalSpace = true;
		gdata1.verticalAlignment = GridData.FILL;
		gdata1.horizontalAlignment = GridData.FILL;
		list.setLayoutData(gdata1);

		Composite c12 = new Composite(composite, SWT.NONE);
		RowLayout rowLayout = new RowLayout();
		rowLayout.wrap = false;
		rowLayout.pack = false;
		rowLayout.justify = false;
		rowLayout.type = SWT.VERTICAL;
		rowLayout.marginLeft = 5;
		rowLayout.marginTop = 5;
		rowLayout.marginRight = 5;
		rowLayout.marginBottom = 5;
		//        rowLayout.spacing = 5;
		c12.setLayout(rowLayout);

		Button newButton = new Button(c12, SWT.PUSH);
		newButton.setText("New");
		newButton.addSelectionListener(new SelectionListener() {
			public void widgetDefaultSelected(SelectionEvent e) {
			}
			public void widgetSelected(SelectionEvent e) {
				InputDialog id =
					new InputDialog(
						getShell(),
						"New project",
						"Enter the new project name",
						"",
						new IInputValidator() {
					public String isValid(String s) {
						String errorMessage =
							s + " is not a correct project name";
						if (s.length() <= 0)
							return "Enter the new project name";
						if (('a' <= s.charAt(0) && s.charAt(0) <= 'z')
							|| ('A' <= s.charAt(0) && s.charAt(0) <= 'Z')) {
							for (int i = 1; i < s.length(); i++)
								if (!(('a' <= s.charAt(i)
									&& s.charAt(i) <= 'z')
									|| ('A' <= s.charAt(i) && s.charAt(i) <= 'Z')
									|| ('0' <= s.charAt(i) && s.charAt(i) <= '9')
									|| '_' == s.charAt(i)))
									return errorMessage;
						}
						if (list.indexOf(s) != -1)
							return s + "is already an existing project";
						return null;
					}
				});
				id.open();
				newProject(id.getValue());
			}
		});
		removeButton = new Button(c12, SWT.PUSH);
		removeButton.setText("Remove");
		removeButton.setEnabled(false);
		removeButton.addSelectionListener(new SelectionListener() {
			public void widgetDefaultSelected(SelectionEvent e) {
			}
			public void widgetSelected(SelectionEvent e) {
				if (MessageDialog
					.openConfirm(
						getShell(),
						"Remove project",
						"Do you really want to delete the project "
							+ list.getSelection()[0]))
					removeProject(list.getSelection()[0]);
			}
		});

		getShell().setText("Choose project");
		return composite;
	}

	protected void okPressed() {
		if (list.getSelectionCount() > 0)
		selectedProject = list.getSelection()[0];
		close();
	}

	String getSelectedProject() {
		return selectedProject;
	}
}
