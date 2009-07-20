//******************************************************************************
/* Copyright (c) 2002, 2003 GEMPLUS Software Research Labs. All Rights Reserved.
/* Copyright (c) 2004 INRIA. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: JpovError.java
/*
/*******************************************************************************
/* Warnings/Remarks:
/******************************************************************************/
package jpov;
import java.util.StringTokenizer;

import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.MultiStatus;
import org.eclipse.core.runtime.Status;
import org.eclipse.jface.dialogs.ErrorDialog;
import org.eclipse.swt.widgets.Shell;

/**
 * Utility class the diplay error dialogs with details
 * @author L. Burdy, A. Requet
 */
public class JpovError {
    
    /**
     * Displays an error dialog with details
     * @param shell The current shell
     * @param title The title of the error dialog
     * @param error The error to displayed
     * @param error_description The error description
     * @param error_details The error details
     **/
	public static void errorDialogWithDetails(
		Shell shell,
		String title,
		String error,
		String error_description,
		String error_details) {
		int c;

		StringTokenizer st = new StringTokenizer(error_details, "\n");

		Status[] s = new Status[c = st.countTokens()];

		for (int i = 0; i < c; i++)
			s[i] =
				new Status(
					IStatus.ERROR,
					"jack.plugin",
					0,
					st.nextToken(),
					null);

		ErrorDialog.openError(
			shell,
			title,
			error,
			new MultiStatus("jack.plugin", 0, s, error_description, null));
	}
}
