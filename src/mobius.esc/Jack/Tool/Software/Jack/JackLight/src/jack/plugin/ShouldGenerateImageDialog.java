//******************************************************************************
//* Copyright (c) 2003, 2004 INRIA. All Rights Reserved.
//*-----------------------------------------------------------------------------
//* Name: SaveMessageDialog.java
//*
//******************************************************************************
//* Warnings/Remarks:
//*****************************************************************************/

package jack.plugin;

import org.eclipse.jface.dialogs.MessageDialog;
import org.eclipse.swt.widgets.Shell;

/**
 * Dialog that indicates that some files need to be saved before an action could 
 * occur.
 *  
 * @author L. Burdy
 **/
public class ShouldGenerateImageDialog extends MessageDialog {


	public static void shouldGenerateImage(
			Shell shell,
			JackProjectPropertyPage jppp) {
			ShouldGenerateImageDialog md =
					new ShouldGenerateImageDialog(shell);
				md.open();
				if (md.getReturnCode() == MessageDialog.CANCEL) {
					return;
				}
				else
					jppp.generateImage();
			}


	
	private ShouldGenerateImageDialog(
		Shell parentShell) {
		super(
			parentShell,
			JackPlugin.DIALOG_TITLE,
			null,
			"You should regenerate the image due to JML Path changes.\n"
				+ "Click 'OK' to generate image now or click 'Cancel'",
			MessageDialog.NONE,
			new String[] { "OK", "Cancel" },
			0);
	}

}
