//******************************************************************************
/* Copyright (c) 2003 INRIA. All Rights Reserved.
 /*------------------------------------------------------------------------------
 /* Name: 
 /*
 /*******************************************************************************
 /* Warnings/Remarks:
 /******************************************************************************/

package jack.plugin.compile;

import jack.plugin.JackPlugin;

import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.QualifiedName;
import org.eclipse.jdt.core.ICompilationUnit;
import org.eclipse.jface.dialogs.MessageDialog;
import org.eclipse.jface.preference.IPreferenceStore;
import org.eclipse.swt.SWT;
import org.eclipse.swt.graphics.Image;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Button;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Control;
import org.eclipse.swt.widgets.Shell;
import org.eclipse.ui.IWorkbenchPart;
import org.eclipse.ui.IWorkbenchPartSite;

/**
 * This class defines a dialog that indicates that some files need to be
 * recompiled.
 * 
 * @author L. Burdy
 */
public class CompileMessageDialog extends MessageDialog {

	static boolean alwaysCompile(String key) {
		IPreferenceStore prefs = JackPlugin.getDefault().getPreferenceStore();
		return prefs.getBoolean(key);
	}

	public static boolean compileRessources(ICompilationUnit cu, IWorkbenchPart activePart, String action, String key,
			QualifiedName property) {
		IWorkbenchPartSite site = activePart.getSite();
		try {
			if (cu.getResource().getPersistentProperty(property) == null
				|| cu.getResource().getPersistentProperty(property).equals("false")) {
				String[] buttons = {"OK", "Cancel"};
				if (property == JackPlugin.JML_COMPILED) {
					if (!alwaysCompile(key)) {
						CompileMessageDialog md = new CompileMessageDialog(site.getShell(), JackPlugin.DIALOG_TITLE,
								null, "File needs to be recompiled.\n" + "Compile the current file before " + action
										+ " ?", MessageDialog.NONE, buttons, 0, action, key);
						md.open();
						if (md.getReturnCode() == MessageDialog.CANCEL) {
							return false;
						}
					}
					PoGenerator.compile(cu);
				} else {
					MessageDialog md = new MessageDialog(site.getShell(), JackPlugin.DIALOG_TITLE, null,
							"File needs to be recompiled.", MessageDialog.NONE, buttons, 0);
					md.open();
					return false;
				}
			}
		} catch (CoreException ce) {
			MessageDialog.openError(site.getShell(), JackPlugin.DIALOG_TITLE, "Error showing view: " + ce.getMessage());
		}
		return true;
	}

	String text, key;
	Button c;
	boolean alwaysCompile;

	private CompileMessageDialog(Shell parentShell, String dialogTitle, Image dialogTitleImage, String dialogMessage,
			int dialogImageType, String[] dialogButtonLabels, int defaultIndex, String text, String key) {
		super(parentShell, dialogTitle, dialogTitleImage, dialogMessage, dialogImageType, dialogButtonLabels,
				defaultIndex);
		this.text = text;
		this.key = key;
	}

	protected Control createCustomArea(Composite parent) {
		Composite co = new Composite(parent, SWT.NONE);
		GridLayout layout = new GridLayout();
		layout.numColumns = 1;
		co.setLayout(layout);

		c = new Button(co, SWT.CHECK);
		c.setSelection(false);
		c.setText("Always compile before " + text);
		return co;
	}

	public int getReturnCode() {
		if (alwaysCompile) {
			IPreferenceStore prefs = JackPlugin.getDefault().getPreferenceStore();
			prefs.setValue(key, true);
		}
		return super.getReturnCode();
	}

	protected void buttonPressed(int buttonId) {
		if (buttonId == MessageDialog.OK)
			alwaysCompile = c.getSelection();
		super.buttonPressed(buttonId);
	}

}
