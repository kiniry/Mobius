///******************************************************************************
//* Copyright (c) 2002, 2003 GEMPLUS Software Research Labs. All Rights Reserved.
//*------------------------------------------------------------------------------
//* Name: ImageContentEditor.java
//*
//********************************************************************************
//* Warnings/Remarks:
//*******************************************************************************/
package jack.plugin;

import jml2b.structure.java.JmlLoader;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.jdt.core.IJavaProject;
import org.eclipse.jface.dialogs.Dialog;
import org.eclipse.jface.dialogs.IInputValidator;
import org.eclipse.jface.dialogs.InputDialog;
import org.eclipse.jface.dialogs.MessageDialog;
import org.eclipse.jface.window.Window;
import org.eclipse.swt.SWT;
import org.eclipse.swt.events.SelectionEvent;
import org.eclipse.swt.events.SelectionListener;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Button;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Control;
import org.eclipse.swt.widgets.List;
import org.eclipse.swt.widgets.Shell;

/**
 * A simple set of widgets allowing to edit the serialized image content.
 * This dialog allows to choose a set of classes that should be added to 
 * the serialized image with their dependencies.
 * 
 * @author A. Requet
 */
public class ImageContentEditor extends Dialog {
	
	private Button addClass;
	private Button removeAll;
	private Button removeSelected;
	private List   classList;
	
	/** The search path that is used for searching classes. */
	private String [] searchPath;
	
	/**
	 * The project to wich the image correspond.
	 */
	private IProject project;
	
	public ImageContentEditor(Shell s, IJavaProject project)
	{
		super(s);
		this.project = project.getProject();
		searchPath = JackPlugin.getJmlPath(project);
	}
	
	/**
	 * Creates the widgets corresponding to the editor.
	 */
	public Control createDialogArea(Composite parent)
	{
		Composite composite = (Composite)super.createDialogArea(parent);
		
		GridLayout layout = new GridLayout();
		layout.numColumns = 2;
		composite.setLayout(layout);
		GridData data;
		classList = new List(composite, SWT.MULTI|SWT.BORDER);
		data = new GridData(GridData.FILL_VERTICAL|GridData.FILL_HORIZONTAL);
		data.grabExcessHorizontalSpace = true;
		data.grabExcessVerticalSpace = true;
		data.horizontalSpan = 1;
		data.verticalSpan = 4;
		classList.setLayoutData(data);
		
		addClass = new Button(composite, SWT.NONE);
		data = new GridData(GridData.FILL_HORIZONTAL);
		data.grabExcessHorizontalSpace = false;
		addClass.setLayoutData(data);
		addClass.setText("Add class...");
		addClass.addSelectionListener(new AddClassListener());
		
		removeSelected = new Button(composite, SWT.NONE);
		data = new GridData(GridData.FILL_HORIZONTAL);
		data.grabExcessHorizontalSpace = false;
		removeSelected.setLayoutData(data);
		
		removeSelected.setText("Remove selected");
		removeSelected.addSelectionListener(new RemoveSelectedListener());
		
		removeAll = new Button(composite, SWT.NONE);
		data = new GridData(GridData.FILL_HORIZONTAL);
		data.grabExcessHorizontalSpace = false;
		removeAll.setLayoutData(data);
		removeAll.setText("Remove all");
		removeAll.addSelectionListener(new RemoveAllListener());
		
		try {
			classList.setItems(JackPlugin.getSerializedImageRoots(project));
		} catch(CoreException e) {
			MessageDialog.openError(getShell(), JackPlugin.DIALOG_TITLE,
				"Error getting serialized image roots: "
				+ e.toString());
		}
	
		getShell().setText("Enter additional classes for the serialized image");
	
		return parent;
	}

	protected void okPressed()
	{
		try {
			JackPlugin.setSerializedImageRoots(project, classList.getItems());
		} catch(CoreException e) {
			MessageDialog.openError(getShell(), JackPlugin.DIALOG_TITLE,
				"Error setting serialized image roots: "
				+ e.toString());			
		}
		super.okPressed();
	}
		
	class RemoveAllListener implements SelectionListener
	{
		public void widgetDefaultSelected(SelectionEvent e)
		{	}
		
		public void widgetSelected(SelectionEvent e)
		{
			// check wether the list is already empty
			if(classList.getItemCount() == 0) {
				return;
			}
			// removes all the items
			classList.removeAll();
		}
	}
	
	class RemoveSelectedListener implements SelectionListener
	{
		public void widgetDefaultSelected(SelectionEvent e)
		{ }
		
		public void widgetSelected(SelectionEvent e)
		{
			if(classList.getSelectionCount() == 0) {
				return;
			}
			classList.remove(classList.getSelectionIndices());
		}
	}
	
	class AddClassListener implements SelectionListener
	{
		public void widgetDefaultSelected(SelectionEvent e)
		{ }
		
		public void widgetSelected(SelectionEvent e)
		{
			// ask for a class
			InputDialog dlg = new InputDialog(getShell(), 
				JackPlugin.DIALOG_TITLE, 
				"Enter the fully qualified name of the class", "", 
				new JmlClassInputValidator());
			if(dlg.open() == Window.OK) {
				// get the class name and adds it to the list
				String class_name = dlg.getValue();
				
				if(!class_name.equals("")) {
					classList.add(class_name);
				}
			}
		}
	}
	
	/**
	 * An input validator that checks that a class exists.
	 */
	class JmlClassInputValidator implements IInputValidator
	{
		/**
		 * Check that given text correspond to the name of a class.
		 * 
		 * @return null if the class exists, an error message if the class does not exists.
		 */
		public String isValid(String text)
		{
			return JmlLoader.classExists(text, searchPath) ? null : text + " is not a valid class name";
		}
	}
}

