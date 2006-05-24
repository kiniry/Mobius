//******************************************************************************
//* Copyright (c) 2003, 2004 INRIA. All Rights Reserved.
//*-----------------------------------------------------------------------------
//* Name: SaveMessageDialog.java
//*
//******************************************************************************
//* Warnings/Remarks:
//*****************************************************************************/

package jack.plugin.edit;

import jack.plugin.JackPlugin;

import java.util.Enumeration;
import java.util.Vector;

import org.eclipse.core.runtime.NullProgressMonitor;
import org.eclipse.jface.dialogs.MessageDialog;
import org.eclipse.jface.preference.IPreferenceStore;
import org.eclipse.swt.SWT;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Button;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Control;
import org.eclipse.swt.widgets.Shell;
import org.eclipse.swt.widgets.Table;
import org.eclipse.swt.widgets.TableItem;
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.IWorkbenchPage;
import org.eclipse.ui.IWorkbenchPart;
import org.eclipse.ui.IWorkbenchPartSite;
import org.eclipse.ui.IWorkbenchWindow;
import org.eclipse.ui.PlatformUI;

/**
 * Dialog that indicates that some files need to be saved before an action could 
 * occur.
 *  
 * @author L. Burdy
 **/
public class SaveMessageDialog extends MessageDialog {

	private static boolean alwaysSave(String key) {
		IPreferenceStore prefs = JackPlugin.getDefault().getPreferenceStore();
		return prefs.getBoolean(key);
	}

	public static boolean saveModifiedRessources(
		IWorkbenchPart activePart,
		String action,
		String key) {
		IWorkbenchPartSite site = activePart.getSite();
		Vector dirty = new Vector();
		IWorkbenchWindow[] wwa =
			PlatformUI.getWorkbench().getWorkbenchWindows();
		for (int i = 0; i < wwa.length; i++) {
			IWorkbenchPage[] wpa = wwa[i].getPages();
			for (int j = 0; j < wpa.length; j++) {
				IEditorPart[] epa = wpa[j].getDirtyEditors();
				for (int k = 0; k < epa.length; k++)
					dirty.add(epa[k]);
			}
		}
		if (dirty.size() > 0 && !alwaysSave(key)) {
			SaveMessageDialog md =
				new SaveMessageDialog(site.getShell(), action, dirty, key);
			md.open();
			if (md.getReturnCode() == MessageDialog.CANCEL) {
				return false;
			}
		}
		Enumeration e = dirty.elements();
		while (e.hasMoreElements()) {
			IEditorPart element = (IEditorPart) e.nextElement();
			element.doSave(new NullProgressMonitor());
		}
		return true;
	}

	/**
	 * Name of the action that requires that save some files.
	 **/
	private String action;

	/**
	 * Sets of dirty editors (<code>org.eclipse.ui.IEditorPart</code>).
	 **/
	private Vector dirty;

	/**
	 * Button allowing to check that all dirty editors have to be saved before
	 * an action.
	 **/
	private Button c;

	/**
	 * Name of preference that stores the fact that all dirty editors have to be
	 * saved before the action.
	 **/
	private String key;

	/**
	 * Button that stores the fact that all dirty editors have to be saved before
	 * an action.
	 **/
	private boolean alwaysSave = false;

	private SaveMessageDialog(
		Shell parentShell,
		String action,
		Vector dirty,
		String key) {
		super(
			parentShell,
			JackPlugin.DIALOG_TITLE,
			null,
			"All modified resources have to be saved before this operation.\n"
				+ "Click 'OK' to confirm or click 'Cancel'",
			MessageDialog.NONE,
			new String[] { "OK", "Cancel" },
			0);
		this.action = action;
		this.dirty = dirty;
		this.key = key;
	}

	protected Control createCustomArea(Composite parent) {
		Composite co = new Composite(parent, SWT.NONE);
		GridLayout layout = new GridLayout();
		layout.numColumns = 1;
		co.setLayout(layout);

		Table list = new Table(co, SWT.SINGLE | SWT.BORDER);

		GridData gdata1 = new GridData(GridData.FILL);
		gdata1.grabExcessHorizontalSpace = true;
		gdata1.grabExcessVerticalSpace = true;
		gdata1.verticalAlignment = GridData.FILL;
		gdata1.horizontalAlignment = GridData.FILL;
		list.setLayoutData(gdata1);

		Enumeration e = dirty.elements();
		TableItem ti[] = new TableItem[dirty.size()];
		int i = 0;
		while (e.hasMoreElements()) {
			IEditorPart element = (IEditorPart) e.nextElement();
			ti[i] = new TableItem(list, SWT.NONE);
			ti[i].setImage(
				element.getEditorInput().getImageDescriptor().createImage());
			ti[i++].setText(element.getEditorInput().getName());
		}
		c = new Button(co, SWT.CHECK);
		c.setSelection(false);
		c.setText(
			"Always save all modified resources automatically prior to "
				+ action);
		return co;
	}

	public int getReturnCode() {
		if (alwaysSave) {
			IPreferenceStore prefs =
				JackPlugin.getDefault().getPreferenceStore();
			prefs.setValue(key, true);
		}
		return super.getReturnCode();
	}

	protected void buttonPressed(int buttonId) {
		if (buttonId == MessageDialog.OK)
			alwaysSave = c.getSelection();
		super.buttonPressed(buttonId);
	}

}
