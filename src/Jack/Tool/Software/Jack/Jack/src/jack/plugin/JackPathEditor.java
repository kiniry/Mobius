//******************************************************************************
/* Copyright (c) 2002, 2003 GEMPLUS Software Research Labs. All Rights Reserved.
/* Copyright (c) 2003, 2004 INRIA. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: JackPathEditor.java
/*
/********************************************************************************
/* Warnings/Remarks:
/*******************************************************************************/
package jack.plugin;

import java.io.File;

import org.eclipse.core.resources.IProject;
import org.eclipse.jdt.core.IClasspathEntry;
import org.eclipse.jdt.core.IJavaProject;
import org.eclipse.jdt.core.JavaModelException;
import org.eclipse.swt.SWT;
import org.eclipse.swt.events.KeyEvent;
import org.eclipse.swt.events.KeyListener;
import org.eclipse.swt.events.SelectionEvent;
import org.eclipse.swt.events.SelectionListener;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Button;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.DirectoryDialog;
import org.eclipse.swt.widgets.FileDialog;
import org.eclipse.swt.widgets.List;
import org.eclipse.swt.widgets.Shell;

/**
 * A dialog that allows editing a list of paths. It is similar to the 
 * <code>org.eclipse.jface.preference.PathEditor</code> class, but is
 * not limited to preferences.
 * 
 * @author A. Requet, L. Burdy
 */
public class JackPathEditor {
	/**
	 * List holding the list of path.
	 */
	private List pathList;

	/**
	 * Button allowing to remove the selected path.
	 */
	private Button removePath;

	/**
	 * Button allowing to move the selected path up.
	 */
	private Button moveUp;

	/**
	 * Button allowing to move the selected path down.
	 */
	private Button moveDown;

	/**
	 * Button allowing to edit the selected path down.
	 */
	private Button edit;
	
	private Button useDefaultClassPathB;

	Button addPathDirectory;
	Button addPathJar;
	/**
	 * The shell that is used when creating dialogs.
	 */
	private Shell shell;

	private JackProjectPropertyPage jppp;

	private boolean useDefaultClassPath;
	
	public JackPathEditor(Shell sh, JackProjectPropertyPage jppp) {
		shell = sh;
		this.jppp = jppp;
	}

	void enableUseDefaultClassPath(boolean status) {
		useDefaultClassPathB.setSelection(status);
		pathList.setEnabled(!status);
		addPathDirectory.setEnabled(!status);
		addPathJar.setEnabled(!status);
		removePath.setEnabled(!status);
		moveUp.setEnabled(!status);
		moveDown.setEnabled(!status);
		edit.setEnabled(!status);
		useDefaultClassPath =  status;
		//imageEditor.setEnabled(status);
	}
	public void createWidgets(Composite parent) {
		GridLayout layout = new GridLayout();
		layout.numColumns = 2;
		parent.setLayout(layout);
		GridData data;
		
		useDefaultClassPathB = new Button(parent, SWT.CHECK);
		useDefaultClassPathB.setText("Use default class path");
//		useDefaultClassPathB.setSelection(JackPlugin.isDefaultClassPathUsed((IProject) ((IJavaProject) jppp.getElement()).getResource()));
		useDefaultClassPathB.addSelectionListener(new SelectionListener() {
			public void widgetSelected(SelectionEvent e) {
				enableUseDefaultClassPath(
useDefaultClassPathB.getSelection());
				jppp.setShouldGenerateImage(true);
			}
			public void widgetDefaultSelected(SelectionEvent e) {}
		});
		data = new GridData(GridData.FILL);
		data.horizontalSpan = 2;
		useDefaultClassPathB.setLayoutData(data);

		
		
		pathList = new List(parent, SWT.SINGLE | SWT.BORDER);
		data = new GridData(GridData.FILL_VERTICAL | GridData.FILL_HORIZONTAL);
		data.grabExcessHorizontalSpace = true;
		data.grabExcessVerticalSpace = true;
		data.horizontalSpan = 1;
		data.verticalSpan = 7;
		pathList.setLayoutData(data);
		pathList.addKeyListener(new PathListKeyListener());

		addPathDirectory = new Button(parent, SWT.NONE);
		data = new GridData(GridData.FILL_HORIZONTAL);
		data.grabExcessHorizontalSpace = false;
		addPathDirectory.setLayoutData(data);
		addPathDirectory.setText("Add D&irectory...");
		addPathDirectory.addSelectionListener(new AddPathDirectoryListener());

		addPathJar = new Button(parent, SWT.NONE);
		data = new GridData(GridData.FILL_HORIZONTAL);
		data.grabExcessHorizontalSpace = false;
		addPathJar.setLayoutData(data);
		addPathJar.setText("Add &Jar or Zip...");
		addPathJar.addSelectionListener(new AddPathJarListener());

		removePath = new Button(parent, SWT.NONE);
		data = new GridData(GridData.FILL_HORIZONTAL);
		data.grabExcessHorizontalSpace = false;
		removePath.setLayoutData(data);
		removePath.setText("&Remove selected");
		removePath.addSelectionListener(new RemoveSelectedListener());

		moveUp = new Button(parent, SWT.NONE);
		data = new GridData(GridData.FILL_HORIZONTAL);
		data.grabExcessHorizontalSpace = false;
		moveUp.setLayoutData(data);
		moveUp.setText("&Up");
		moveUp.addSelectionListener(new MoveElementListener(-1));

		moveDown = new Button(parent, SWT.NONE);
		data = new GridData(GridData.FILL_HORIZONTAL);
		data.grabExcessHorizontalSpace = false;
		moveDown.setLayoutData(data);
		moveDown.setText("D&own");
		moveDown.addSelectionListener(new MoveElementListener(+1));
		
		edit = new Button(parent, SWT.NONE);
		data = new GridData(GridData.FILL_HORIZONTAL);
		data.grabExcessHorizontalSpace = false;
		edit.setLayoutData(data);
		edit.setText("E&dit");
		edit.addSelectionListener(new EditElementListener());
		
		enableUseDefaultClassPath(JackPlugin.isDefaultClassPathUsed((IProject) ((IJavaProject) jppp.getElement()).getResource()));
	}

	/**
	 * Returns the path list as an array of <code>String</code>.
	 *  
	 * @return the path list.
	 */
	public String[] getPath() {
		if (useDefaultClassPath) {
			try {
				IClasspathEntry[] icpea =  ((IJavaProject) jppp.getElement()).getResolvedClasspath(false);
				String[] res = new String[icpea.length];
				for (int i=0; i < icpea.length; i++)
					switch (icpea[i].getEntryKind()) {
						case IClasspathEntry.CPE_SOURCE :
							res[i] = ((IJavaProject) jppp.getElement()).getProject().getLocation().toOSString();
						break;
						case IClasspathEntry.CPE_LIBRARY :
							res[i] = icpea[i].getPath().toString();
					break;
					}
//			res[i] = icpea[i].getPath().toString();
				
				return res;
			}
			catch (JavaModelException jme) {
				return new String[0];
			}
		}
		else
			return pathList.getItems();
	}

	/**
	 * Set the path list to the given one.
	 * 
	 * @param new_path the new path list. This parameter should not be <code>null</code>.
	 */
	//@ requires new_path != null;
	public void setPath(String[] new_path) {
		pathList.setItems(new_path);
	}

	Shell getShell() {
		return shell;
	}

	/**
	 * <code>SelectionListener</code> allowing to move elements up or down
	 * in the list.
	 * <p>
	 * Note that the direction of the <code>SelectionListener</code> is 
	 * defined at creation time. Thus, if it is needed to move elements up
	 * and down, two different <code>MoveElementListener</code> have to be 
	 * used.
	 */
	class MoveElementListener implements SelectionListener {
		/** 
		 * The relative displacement of the selected element. 
		 * The widgetSelected method will move the selected element of 
		 * <code>delta</code> positions in the list.
		 * <p>
		 * Typical values for <code>delta</code> would be 1 or -1.
		 */
		private int delta;

		public MoveElementListener(int delta) {
			this.delta = delta;
		}

		public void widgetDefaultSelected(SelectionEvent e) {
		}

		public void widgetSelected(SelectionEvent e) {
			// get index of selected element
			int selected = pathList.getSelectionIndex();

			if (selected == -1) {
				// abort if no item is selected
				return;
			}

			int count = pathList.getItemCount();

			// ensures that the element can be moved
			int destination = selected + delta;
			if (destination >= count || destination < 0) {
				// element cannot be moved
				return;
			}

			// moves the selected element. this is performed by removing the
			// element, and adding it at the destination position
			String element = pathList.getItem(selected);
			pathList.remove(selected);
			pathList.add(element, destination);
			pathList.select(destination);
			jppp.setShouldGenerateImage(true);
		}
	}

	/**
	 * <code>SelectionListener</code> allowing to remove the selected
	 * elements.
	 */
	class RemoveSelectedListener implements SelectionListener {
		public void widgetDefaultSelected(SelectionEvent e) {
		}

		public void widgetSelected(SelectionEvent e) {
			int selected = pathList.getSelectionIndex();
			if (selected != -1) {
				pathList.remove(selected);
				// select the next element if possible
				if (selected < pathList.getItemCount()) {
					pathList.select(selected);
				} else if (selected > 0) {
					pathList.select(selected - 1);
				}
				jppp.setShouldGenerateImage(true);
			}
		}
	}

	/**
	 * <code>SelectionListener</code> allowing to edit the selected
	 * elements.
	 */
	class EditElementListener implements SelectionListener {
		public void widgetDefaultSelected(SelectionEvent e) {
		}

		public void widgetSelected(SelectionEvent e) {
			int selected = pathList.getSelectionIndex();
			if (selected != -1) {
				if (new File(pathList.getItem(selected)).isDirectory()) {
					DirectoryDialog dialog = new DirectoryDialog(getShell());
					dialog.setFilterPath(pathList.getItem(selected));
					String path = dialog.open();
					if (path != null) {
						pathList.setItem(selected, path);
					}
				}
				else {
					FileDialog dialog = new FileDialog(getShell());
					dialog.setFileName(pathList.getItem(selected));
					String path = dialog.open();
					if (path != null) {
						pathList.setItem(selected, path);
					}
				}
			}
		}
	}
	/**
	 * SelectionListener allowing to add new path to the list of paths.
	 */
	class AddPathDirectoryListener implements SelectionListener {
		DirectoryDialog dialog;

		public void widgetDefaultSelected(SelectionEvent e) {
		}

		public void widgetSelected(SelectionEvent e) {
			if (dialog == null) {
				dialog = new DirectoryDialog(getShell());
			}
			String path = dialog.open();
			if (path != null) {
				// add and select the path
				pathList.add(path, 0);
				pathList.select(0);
				jppp.setShouldGenerateImage(true);
			}
		}
	}

	/**
	 * SelectionListener allowing to add new path to the list of paths.
	 */
	class AddPathJarListener implements SelectionListener {
		FileDialog dialog;
		String ext;

		public void widgetDefaultSelected(SelectionEvent e) {
		}

		public void widgetSelected(SelectionEvent e) {
			if (dialog == null) {
				dialog = new FileDialog(getShell());
			}
			dialog.setFilterExtensions(new String[] { "*.jar", "*.zip" });
			String path = dialog.open();
			if (path != null) {
				// add and select the path
				pathList.add(path, 0);
				pathList.select(0);
				jppp.setShouldGenerateImage(true);
			}
		}
	}

	class PathListKeyListener implements KeyListener {

		public void keyPressed(KeyEvent e) {
			if (e.keyCode == SWT.DEL) {
				int selected = pathList.getSelectionIndex();
				if (selected != -1) {
					pathList.remove(selected);
					// select the next element if possible
					if (selected < pathList.getItemCount()) {
						pathList.select(selected);
					} else if (selected > 0) {
						pathList.select(selected - 1);
					}
				}
			}
		}

		public void keyReleased(KeyEvent e) {
		}

	}
	
	public boolean isUseDefaultClassPath() {
		return useDefaultClassPath;
	}
}
