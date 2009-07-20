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
import org.eclipse.jface.preference.StringFieldEditor;
import org.eclipse.ui.IWorkbench;
import org.eclipse.ui.IWorkbenchPreferencePage;

/**
 * This class implements the preference page for the compiler.
 * 
 * @author L. Burdy
 **/
public class JackPreferencePageCompiler
	extends FieldEditorPreferencePage
	implements IWorkbenchPreferencePage {

	/**
	 * Creates the JackPreferencePage for the compiler.
	 */
	public JackPreferencePageCompiler() {
		super(GRID);
		setPreferenceStore(JackPlugin.getDefault().getPreferenceStore());
		setDescription("Preferences for the compiler");

	}
	
	/**
	 * Creates the field editors. Field editors are abstractions of
	 * the common GUI blocks needed to manipulate various types
	 * of preferences. Each field editor knows how to save and
	 * restore itself.
	 **/
	public void createFieldEditors() {
		addField(
			new StringFieldEditor(
				JackPlugin.JACK_SUBDIRECTORY,
				"&Default subdirectory for Jack Files:",
				getFieldEditorParent()));
//		addField(
//			new PathEditor(
//				JackPlugin.JMLPATH_PREFERENCE,
//				"Default &JML search path:",
//				"Choose directory",
//				getFieldEditorParent()));
		addField(
			new BooleanFieldEditor(
				JackPlugin.JACK_OBVIOUS_PO,
				"Generate obvious lemmas",
				BooleanFieldEditor.SEPARATE_LABEL,
				getFieldEditorParent()));
		addField(
			new BooleanFieldEditor(
				JackPlugin.JACK_WELLDEF_LEMMA,
				"Generate well definedness lemmas",
				BooleanFieldEditor.SEPARATE_LABEL,
				getFieldEditorParent()));
		Enumeration e = Languages.getLanguagesNames();
		while (e.hasMoreElements()) {
			String name = (String) e.nextElement();
			if (Languages.getPrinterClass(name) != null)
				addField(
					new BooleanFieldEditor(
						JackPlugin.JACK_GENERATE + name,
						"Generate " + name + " output file",
						BooleanFieldEditor.SEPARATE_LABEL,
						getFieldEditorParent()));
		}
	}

	public void init(IWorkbench workbench) {
	}

}
