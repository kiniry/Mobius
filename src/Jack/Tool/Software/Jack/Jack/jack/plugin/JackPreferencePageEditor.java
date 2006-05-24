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
import org.eclipse.jface.preference.ColorFieldEditor;
import org.eclipse.jface.preference.FieldEditorPreferencePage;
import org.eclipse.jface.preference.FontFieldEditor;
import org.eclipse.ui.IWorkbench;
import org.eclipse.ui.IWorkbenchPreferencePage;

/**
 * This class implements the preference page for the editor.
 * 
 * @author L. Burdy
 **/
public class JackPreferencePageEditor
	extends FieldEditorPreferencePage
	implements IWorkbenchPreferencePage {
		
	/**
	 * Creates the JackPreferencePage for the editor.
	 */
	public JackPreferencePageEditor() {
		super(GRID);
		setPreferenceStore(JackPlugin.getDefault().getPreferenceStore());
		setDescription("Preferences for the lemma viewer");

	}
	
	/**
	 * Creates the field editors. Field editors are abstractions of
	 * the common GUI blocks needed to manipulate various types
	 * of preferences. Each field editor knows how to save and
	 * restore itself.
	 */
	public void createFieldEditors() {
		addField(
			new FontFieldEditor(
				JackPlugin.JACK_VIEWER_FONT,
				"Font for Jack Viewer (changes on next restart):",
				getFieldEditorParent()));
		Enumeration e = Languages.getLanguagesNames();
		while (e.hasMoreElements()) {
			String name = (String) e.nextElement();
			addField(
				new BooleanFieldEditor(
					JackPlugin.JACK_VIEW_SHOW + name,
					"Show " + name + " view",
					BooleanFieldEditor.SEPARATE_LABEL,
					getFieldEditorParent()));
			
		}		
		addField(
			new ColorFieldEditor(
				JackPlugin.MULTI_COMMENT_JML_COLOR,
				"Multi-line JML comment color",
				getFieldEditorParent()));
		addField(
			new ColorFieldEditor(
				JackPlugin.SINGLE_COMMENT_JML_COLOR,
				"Single-line JML comment color",
				getFieldEditorParent()));
		addField(
			new ColorFieldEditor(
				JackPlugin.JML_KEYWORD_COLOR,
				"JML keyword color",
				getFieldEditorParent()));
	}
	
	public void init(IWorkbench workbench) {
	}

}
