//******************************************************************************
/* Copyright (c) 2002, 2003 GEMPLUS Software Research Labs. All Rights Reserved.
/* Copyright (c) 2003, 2004 INRIA. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: JackProjectPropertyPage.java
/*
/********************************************************************************
/* Warnings/Remarks:
/*******************************************************************************/
package jack.plugin;

import jack.util.Logger;

import java.io.File;
import java.lang.reflect.InvocationTargetException;

import jml2b.structure.java.JmlLoader;

import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.jdt.core.IJavaProject;
import org.eclipse.jface.dialogs.IInputValidator;
import org.eclipse.jface.dialogs.InputDialog;
import org.eclipse.jface.dialogs.MessageDialog;
import org.eclipse.jface.dialogs.ProgressMonitorDialog;
import org.eclipse.jface.preference.IPreferenceStore;
import org.eclipse.jface.window.Window;
import org.eclipse.swt.SWT;
import org.eclipse.swt.events.SelectionEvent;
import org.eclipse.swt.events.SelectionListener;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Button;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Control;
import org.eclipse.swt.widgets.Label;
import org.eclipse.swt.widgets.List;
import org.eclipse.swt.widgets.TabFolder;
import org.eclipse.swt.widgets.TabItem;
import org.eclipse.swt.widgets.Text;
import org.eclipse.ui.dialogs.PropertyPage;

/**
 * Property page for Java projects.
 * <p>
 * 
 * @author A. Requet, L. Burdy
 */
public class JackProjectPropertyPage extends PropertyPage {

	private Button addClass;
	private Button removeAll;
	private Button removeSelected;
	private List   classList;
	private String [] searchPath;
	private Text editedPath;

	/**
	 * Editor used to edit the jml search path.
	 */
	private JackPathEditor jmlPathEditor;

	/**
	 * Editor used to edit default jml specification.
	 */
	private JackDefaultSpecEditor defaultSpecEditor;

	/** 
	 * Check item allowing to toggle the use of a serialized image 
	 * on/off.
	 */
	private Button useSerializedImageButton;

	/**
	 * Button allowing to generate the serialized image.
	 */
	private Button generateImageButton;

	private boolean shouldGenerateImage = false;

	public void setShouldGenerateImage(boolean shouldGenerateImage) {
		this.shouldGenerateImage = shouldGenerateImage;
	}
	
	boolean setUseImage(boolean new_value) {
		IJavaProject project = (IJavaProject) getElement();
		IResource resource = project.getResource();

		try {
			resource.setPersistentProperty(
				JackPlugin.USE_SERIALIZED_IMAGE_PROPERTY,
				new_value ? "true" : "false");
			return true;
		} catch (CoreException e) {
			Logger.err.println("Exception catched: " + e.toString());
			return false;
		}
	}

	boolean useImage() {
		IJavaProject project = (IJavaProject) getElement();
		IResource resource = project.getResource();

		try {
			String value =
				resource.getPersistentProperty(
					JackPlugin.USE_SERIALIZED_IMAGE_PROPERTY);
			if (value == null || !value.equals("true")) {
				return false;
			}
			return true;
		} catch (CoreException e) {
			Logger.err.println("CoreException catched: " + e.toString());
			return false;
		}
	}

	private String getJackPath() {
		IJavaProject project = (IJavaProject) getElement();
		IResource resource = project.getResource();
		JackPlugin plugin = JackPlugin.getDefault();

		return plugin.getProperty(
			resource,
			JackPlugin.JACK_DIR_PROPERTY,
			JackPlugin.JACK_SUBDIRECTORY);
	}

	/**
	 * Returns the output folder, creating it if it does not exists yet.
	 * 
	 * @return the output folder used by the Jack plugin.
	 */
	private IFolder getAndCreateOutputDir() {
		IJavaProject java_project = (IJavaProject) getElement();
		IProject project = java_project.getProject();

		// get the output directory
		IPreferenceStore prefs = JackPlugin.getDefault().getPreferenceStore();
		String output_dir = prefs.getString(JackPlugin.JACK_SUBDIRECTORY);

		IFolder po_dir = project.getFolder(output_dir);
		if (!po_dir.exists()) {
			try {
				// create the folder if it does not exists
				po_dir.create(false, true, null);
			} catch (CoreException e) {
				return null;
			}
		}
		return po_dir;
	}

	private IProject getProject() {
		IJavaProject java_project = (IJavaProject) getElement();
		return java_project.getProject();
	}

	
/*	void setPathAndGenerateImage() {
		IJavaProject java_project = (IJavaProject) getElement();
		IProject project = (IProject) java_project.getResource();
		// sets the content of the JmlPath variable
		try {
			JackPlugin.setJmlPath(project, jmlPathEditor.getPath());
		} catch (CoreException e) {
			MessageDialog.openError(
				getShell(),
				JackPlugin.DIALOG_TITLE,
				"Error setting properties: " + e.toString());
			}
		generateImage();
	}
*/	
	/**
	 * Generates the serialized image.
	 */
	void generateImage() {
		IFolder folder = getAndCreateOutputDir();
		File folder_file = folder.getLocation().toFile();
		File output_file = new File(folder_file, JackPlugin.IMAGE_NAME);
		IJavaProject java_project = (IJavaProject) getElement();
//		IProject project = (IProject) java_project.getResource();

/*		ImageContentEditor image_dialog =
			new ImageContentEditor(getShell(), project);
*/
/*		if (image_dialog.open() != Window.OK) {
			// stop here
			return;
		}
*/
		// now, generates the image
		ImageGenerator generator = new ImageGenerator(java_project, output_file);
		generator.setClasses(classList.getItems());

		ProgressMonitorDialog dlg = new ProgressMonitorDialog(getShell());

		try {
			dlg.run(true, true, generator);
		} catch (InvocationTargetException e) {
			Throwable t = e.getTargetException();
			Logger.err.println("InvocationTargetException : " + t.toString());
			t.printStackTrace();
			MessageDialog.openInformation(
				getShell(),
				JackPlugin.DIALOG_TITLE,
				"InvocationTargetException catched : " + t.toString());
		} catch (Exception e) {
			MessageDialog.openInformation(
				getShell(),
				JackPlugin.DIALOG_TITLE,
				"Exception catched (JackPopup.run()): " + e.toString());
			return;
		}

		// in case of error, explain why
		if (!generator.hasSucceeded()) {
			MessageDialog.openInformation(
				getShell(),
				JackPlugin.DIALOG_TITLE,
				generator.getErrorDescription());
		}
		else
			shouldGenerateImage = false;

		try {
			folder.refreshLocal(IResource.DEPTH_INFINITE, null);
		} catch (CoreException e) {
			MessageDialog.openInformation(
				getShell(),
				JackPlugin.DIALOG_TITLE,
				("Could not refresh Jack directory : " + e.toString()));
		}
	}

	/**
	 * @see PreferencePage#createContents(Composite)
	 */
	protected Control createContents(Composite parent) {
		IJavaProject java_project = (IJavaProject) getElement();
		IProject project = (IProject) java_project.getResource();
		searchPath = JackPlugin.getJmlPath(java_project);
		
		Composite composite = new Composite(parent, SWT.NONE);
		GridLayout layout = new GridLayout();
		layout.numColumns = 3;

		composite.setLayout(layout);
		GridData data;

		Label path_label = new Label(composite, SWT.NONE);
		path_label.setText("Subdirectory for Jack files:");
		data = new GridData(GridData.FILL);
		path_label.setLayoutData(data);

		editedPath = new Text(composite, SWT.SINGLE | SWT.BORDER);
		editedPath.setText(getJackPath());
		data = new GridData(GridData.FILL_HORIZONTAL);
		data.horizontalSpan = 2;
		editedPath.setLayoutData(data);

		TabFolder tf = new TabFolder(composite, SWT.NONE);
		data = new GridData(GridData.FILL_HORIZONTAL | GridData.FILL_VERTICAL);
		data.horizontalSpan = 3;
		tf.setLayoutData(data);

		TabItem jml = new TabItem(tf, 0);
		jml.setText("Jml path");
		TabItem serIm = new TabItem(tf, 1);
		serIm.setText("Serialized image");
			TabItem defaultClauses = new TabItem(tf, 2);
		defaultClauses.setText("Jml specification");

	
		
		Composite composite1 = new Composite(tf, SWT.NONE);
		serIm.setControl(composite1);
	
		layout = new GridLayout();
		layout.numColumns = 2;
		composite1.setLayout(layout);

		useSerializedImageButton = new Button(composite1, SWT.CHECK);
		useSerializedImageButton.setText("Use serialised image");
		useSerializedImageButton.addSelectionListener(new SelectionListener() {
			public void widgetSelected(SelectionEvent e) {
				enableUseSerializedImage(
					useSerializedImageButton.getSelection());
			}
			public void widgetDefaultSelected(SelectionEvent e) {}
		});
		data = new GridData(GridData.FILL);
		data.horizontalSpan = 1;
		useSerializedImageButton.setLayoutData(data);

		generateImageButton = new Button(composite1, SWT.NONE);
		generateImageButton.setText("&Generate image");
		generateImageButton.addSelectionListener(new SelectionListener() {
			public void widgetSelected(SelectionEvent e) {
				generateImage();
			}
			public void widgetDefaultSelected(SelectionEvent e) {}
		});
		data = new GridData(GridData.FILL);
		data.horizontalSpan = 1;
		generateImageButton.setLayoutData(data);

			Label addClassL = new Label(composite1, SWT.NONE);
		addClassL.setText("Additional classes for the serialized image");
		data = new GridData(GridData.FILL_HORIZONTAL);
		data.horizontalSpan = 2;
		addClassL.setLayoutData(data);

		classList = new List(composite1, SWT.MULTI|SWT.BORDER);
		data = new GridData(GridData.FILL_VERTICAL|GridData.FILL_HORIZONTAL);
		data.grabExcessHorizontalSpace = true;
		data.grabExcessVerticalSpace = true;
		data.horizontalSpan = 1;
		data.verticalSpan = 4;
		classList.setLayoutData(data);
		
		addClass = new Button(composite1, SWT.NONE);
		data = new GridData(GridData.FILL_HORIZONTAL);
		data.grabExcessHorizontalSpace = false;
		addClass.setLayoutData(data);
		addClass.setText("Add class...");
		addClass.addSelectionListener(new AddClassListener());
		
		removeSelected = new Button(composite1, SWT.NONE);
		data = new GridData(GridData.FILL_HORIZONTAL);
		data.grabExcessHorizontalSpace = false;
		removeSelected.setLayoutData(data);
		removeSelected.setText("Remove selected");
		removeSelected.addSelectionListener(new RemoveSelectedListener());
		
		removeAll = new Button(composite1, SWT.NONE);
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
		
		Composite path_group = new Composite(tf, SWT.NONE);
		jml.setControl(path_group);

		jmlPathEditor = new JackPathEditor(getShell(), this);
		jmlPathEditor.createWidgets(path_group);

		IJavaProject jprj = (IJavaProject) getElement();

		jmlPathEditor.setPath(JackPlugin.getJmlPath(jprj));

		Composite default_comp = new Composite(tf, SWT.NONE);
		defaultClauses.setControl(default_comp);

		defaultSpecEditor = new JackDefaultSpecEditor(getShell(), this);
		defaultSpecEditor.createWidgets(default_comp);
		defaultSpecEditor.updateControls(getProject());

		enableUseSerializedImage(useImage());
		shouldGenerateImage = false;

		return composite;
	}

	/**
	 * Applies the changes performed in the dialog.
	 */
	public boolean performOk() {
		setUseImage(useSerializedImageButton.getSelection());

		IJavaProject java_project = (IJavaProject) getElement();
		IProject project = (IProject) java_project.getResource();

		// sets the content of the JmlPath variable
		try {
			JackPlugin.setJmlPath(project, jmlPathEditor.isUseDefaultClassPath(), jmlPathEditor.getPath());
			JackPlugin.setSerializedImageRoots(project, classList.getItems());
		} catch (CoreException e) {
			MessageDialog.openError(
				getShell(),
				JackPlugin.DIALOG_TITLE,
				"Error setting properties: " + e.toString());
			return false;
		}

		if (shouldGenerateImage)
			ShouldGenerateImageDialog.shouldGenerateImage(getShell(), this);
		shouldGenerateImage = false;
		return defaultSpecEditor.performOk(project);

		// AR: check that the image is generated if we want to use an image,
		// and ask for generating the images.
	}

	/**
	 * Enables or disables the use of a serialized image. This method only 
	 * updates the widgets and does not save the result.
	 * 
	 * The result must be saved by the performOk function.
	 */
	void enableUseSerializedImage(boolean status) {
		useSerializedImageButton.setSelection(status);
		generateImageButton.setEnabled(status);
		addClass.setEnabled(status);
		removeAll.setEnabled(status);
		removeSelected.setEnabled(status);
		classList.setEnabled(status);
		shouldGenerateImage =  status;
		//imageEditor.setEnabled(status);
	}

	/**
	 * @return
	 */
	public boolean isImageUsed() {
		return useSerializedImageButton.getSelection();
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
