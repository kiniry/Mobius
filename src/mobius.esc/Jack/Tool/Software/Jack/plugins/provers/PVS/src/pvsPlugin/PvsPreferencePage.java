//******************************************************************************
/* Copyright (c) 2003, 2004 INRIA. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: 
/*
/*******************************************************************************
/* Warnings/Remarks:
/******************************************************************************/

package pvsPlugin;

import org.eclipse.jface.preference.FieldEditorPreferencePage;
import org.eclipse.jface.preference.FileFieldEditor;
import org.eclipse.jface.preference.StringFieldEditor;
import org.eclipse.ui.IWorkbench;
import org.eclipse.ui.IWorkbenchPreferencePage;

/**
 * @author L. Burdy
 **/
public class PvsPreferencePage
	extends FieldEditorPreferencePage
	implements IWorkbenchPreferencePage {

	/**
	 * Creates the JackPreferencePage for provers settings.
	 */
	public PvsPreferencePage() {
		super(GRID);
		setPreferenceStore(PvsPlugin.getDefault().getPreferenceStore());
		setDescription("Preferences for the PVS prover");

	}
	/**
	 * Creates the field editors. Field editors are abstractions of
	 * the common GUI blocks needed to manipulate various types
	 * of preferences. Each field editor knows how to save and
	 * restore itself.
	 */
	public void createFieldEditors() {
		addField(
			new FileFieldEditor(
				PvsPlugin.PVS_EXE,
				"PVS executable",
				true,
				getFieldEditorParent()));
		addField(
					new StringFieldEditor(
						PvsPlugin.PVS_EXE_OPTIONS,
						"PVS executable options",
						getFieldEditorParent()));

	}

	public void init(IWorkbench workbench) {
	
	}

}
