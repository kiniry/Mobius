//******************************************************************************
/* Copyright (c) 2002, 2003 GEMPLUS Software Research Labs. All Rights Reserved.
/* Copyright (c) 2003, 2004 INRIA. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: JackPreferencePage.java
/*
/********************************************************************************
/* Warnings/Remarks:
/*  09/26/2003 : Simplify integration achieved
/*******************************************************************************/
package jack.plugin;

import org.eclipse.jface.preference.FieldEditorPreferencePage;
import org.eclipse.ui.IWorkbench;
import org.eclipse.ui.IWorkbenchPreferencePage;

/**
 * This class defines the Preferences page for <b>Jack</b>,
 * the <b>J</b>ava <b>A</b>pplets <b>C</b>orrectness <b>K</b>it.
 * <p>
 * This class represents a preference page that
 * is contributed to the Preferences dialog. By 
 * subclassing <samp>FieldEditorPreferencePage</samp>, we
 * can use the field support built into JFace that allows
 * us to create a page that is small and knows how to 
 * save, restore and apply itself.
 * <p>
 * This page is used to modify preferences only. They
 * are stored in the preference store that belongs to
 * the main plug-in class. That way, preferences can
 * be accessed directly via the preference store.
 * 
 * @author A. Requet, L. Burdy
 **/
public class JackPreferencePage
	extends FieldEditorPreferencePage
	implements IWorkbenchPreferencePage {

	/**
	 * Creates the JackPreferencePage.
	 */
	public JackPreferencePage() {
		super(GRID);
		//setPreferenceStore(JackPlugin.getDefault().getPreferenceStore());
		setDescription("Preferences for the Java Applet Correctness Kit");

		// should already be initialised by PogPlugin
		// initializeDefaults();
	}

	/**
	 * Creates the field editors. Field editors are abstractions of
	 * the common GUI blocks needed to manipulate various types
	 * of preferences. Each field editor knows how to save and
	 * restore itself.
	 */
	public void createFieldEditors() {
	}

	public void init(IWorkbench workbench) {


	}
}