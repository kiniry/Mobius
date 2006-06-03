//******************************************************************************
/* Copyright (c) 2002, 2003 GEMPLUS Software Research Labs. All Rights Reserved.
/* Copyright (c) 2003, 2004 INRIA. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: CompileButton.java
/*
/********************************************************************************
/* Warnings/Remarks:
/*******************************************************************************/
package jack.plugin.compile;

import jack.plugin.JackPlugin;
import jack.plugin.ToolbarButton;
import jack.plugin.edit.SaveMessageDialog;
import jack.util.Logger;

import java.lang.reflect.InvocationTargetException;

import org.eclipse.jdt.ui.JavaUI;
import org.eclipse.jface.action.IAction;
import org.eclipse.jface.dialogs.MessageDialog;
import org.eclipse.jface.dialogs.ProgressMonitorDialog;
import org.eclipse.swt.widgets.Shell;
import org.eclipse.ui.PartInitException;

/**
 * Action allowing to compile 
 * @author A. Requet, L. Burdy
 */
public class CompileButton extends ToolbarButton {

	public void run(IAction action) {
		Shell sh = getWindow().getShell();

		try {
			getWindow().getActivePage().showView(JavaUI.ID_PACKAGES);
		} catch (PartInitException e) {
			MessageDialog.openError(
				sh,
				JackPlugin.DIALOG_TITLE,
				"Error showing view: " + e.toString());
			return;
		}

		if (getSelection() == null) {
			MessageDialog.openInformation(
				sh,
				JackPlugin.DIALOG_TITLE,
				"You should select a JML file first");
			return;
		}

		if (!SaveMessageDialog
			.saveModifiedRessources(
				getWindow().getActivePage().getActivePart(),
				"compiling",
				JackPlugin.ALWAYS_SAVE_BEFORE_COMPILING))
			return;

		PoGenerator pog = new PoGenerator(getSelection().iterator());

		ProgressMonitorDialog dlg = new ProgressMonitorDialog(sh);

		try {
			dlg.run(true, true, pog);
		} catch (InvocationTargetException e) {
			Throwable t = e.getTargetException();
			Logger.err.println("InvocationTargetException : " + t.toString());
			t.printStackTrace();
			MessageDialog.openInformation(
				sh,
				JackPlugin.DIALOG_TITLE,
				"InvocationTargetException catched : " + t.toString());
		} catch (Exception e) {
			MessageDialog.openInformation(
				sh,
				JackPlugin.DIALOG_TITLE,
				"Exception catched (JackPopup.run()): " + e.toString());
			return;
		}

		// in case of error, explain why
		if (!pog.hasSucceeded()) {
			MessageDialog.openInformation(
				sh,
				JackPlugin.DIALOG_TITLE,
				pog.getErrorDescription());
		}
	}
}
