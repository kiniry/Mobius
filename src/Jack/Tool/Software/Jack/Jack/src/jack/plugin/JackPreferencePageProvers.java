//******************************************************************************
/* Copyright (c) 2003, 2004 INRIA. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: 
/*
/*******************************************************************************
/* Warnings/Remarks:
/******************************************************************************/

package jack.plugin;

import java.util.Enumeration;

import jml2b.languages.Languages;

import org.eclipse.jface.preference.BooleanFieldEditor;
import org.eclipse.jface.preference.FieldEditorPreferencePage;
import org.eclipse.jface.preference.IntegerFieldEditor;
import org.eclipse.ui.IWorkbench;
import org.eclipse.ui.IWorkbenchPreferencePage;

/**
 * This class implements the generic preference page for the provers.
 * 
 * @author L. Burdy
 **/
public class JackPreferencePageProvers
	extends FieldEditorPreferencePage
	implements IWorkbenchPreferencePage {

	/**
	 * Creates the JackPreferencePage for provers settings.
	 */
	public JackPreferencePageProvers() {
		super(GRID);
		setPreferenceStore(JackPlugin.getDefault().getPreferenceStore());
		setDescription("Preferences for the provers");

	}
	/**
	 * Creates the field editors. Field editors are abstractions of
	 * the common GUI blocks needed to manipulate various types
	 * of preferences. Each field editor knows how to save and
	 * restore itself.
	 */
	public void createFieldEditors() {
		addField(
			new IntegerFieldEditor(
				JackPlugin.JACK_PROOF_TASK_MAX_RUNNING,
				"Number of parallel proof tasks",
				getFieldEditorParent()));
		Enumeration e = Languages.getLanguagesNames();
		while (e.hasMoreElements()) {
			String name = (String) e.nextElement();
			if (Languages.getObviousProverClass(name) != null)
				addField(
					new BooleanFieldEditor(
						JackPlugin.OBVIOUS_PROVER + name,
						"Use " + name + " obvious prover",
						BooleanFieldEditor.SEPARATE_LABEL,
						getFieldEditorParent()));
		}
	}

	public void init(IWorkbench workbench) {
	}

}
