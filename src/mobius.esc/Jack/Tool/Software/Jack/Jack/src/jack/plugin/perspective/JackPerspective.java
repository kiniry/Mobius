//******************************************************************************
/* Copyright (c) 2003 INRIA. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: 
/*
/*******************************************************************************
/* Warnings/Remarks:
/******************************************************************************/

package jack.plugin.perspective;

import jack.plugin.JackPlugin;

import org.eclipse.jdt.ui.JavaUI;
import org.eclipse.ui.IFolderLayout;
import org.eclipse.ui.IPageLayout;
import org.eclipse.ui.IPerspectiveFactory;

/**
 * The Jack perspective.
 * 
 * @author L. Burdy
 **/
public class JackPerspective implements IPerspectiveFactory {

	public void createInitialLayout(IPageLayout layout) {
		// Get the editor area.
		String editorArea = layout.getEditorArea();

		layout.setEditorAreaVisible(false);

		IFolderLayout topRight =
			layout.createFolder("topRight", IPageLayout.TOP, 0.66f, editorArea);
		topRight.addView(JackPlugin.SOURCE_CASE_VIEWER_ID);

		IFolderLayout bottom =
			layout.createFolder(
				"bottom",
				IPageLayout.BOTTOM,
				0.66f,
				"topRight");
		bottom.addView(JackPlugin.JACK_METRICS_VIEW_ID);
		bottom.addView(JackPlugin.JACK_PROOF_VIEW_ID);
		bottom.addView(JackPlugin.LEMMA_VIEWER);

		// Top left: 
		IFolderLayout topLeft =
			layout.createFolder("topLeft", IPageLayout.LEFT, 0.25f, "topRight");
		topLeft.addView(JavaUI.ID_PACKAGES);
		topLeft.addView(JackPlugin.CASE_EXPLORER_VIEW_ID);
	}

}
