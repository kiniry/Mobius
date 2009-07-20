//******************************************************************************
/* Copyright (c) 2003, 2004 INRIA. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: 
/*
/*******************************************************************************
/* Warnings/Remarks:
/******************************************************************************/

package coqPlugin;

import org.eclipse.jface.preference.BooleanFieldEditor;
import org.eclipse.jface.preference.FieldEditorPreferencePage;
import org.eclipse.jface.preference.FileFieldEditor;
import org.eclipse.jface.preference.IPreferenceStore;
import org.eclipse.ui.IWorkbench;
import org.eclipse.ui.IWorkbenchPreferencePage;

/**
 * @author L. Burdy
 **/
public class PreferencePage
	extends FieldEditorPreferencePage
	implements IWorkbenchPreferencePage {

	public static final String COQ_MUSTPROVEALL_TOUGH = "coqMustProveAllLight";
	public static final String COQ_MUSTPROVEALL_LIGHT = "coqMustProveAllTough";
	public static final String COQ_SEMIAUTO_LOC = "coqSemiAutoLocation";
	public static final String COQ_USECUSTOMCOQ = "coqCustomTactics";
	
	public static final String COQ_DUMBSTYLEPREL = "coqDumbStylePrelude";
	public static final String COQ_PRETTYPRINTER = "coqPrettyPrinter";
	

	private static IPreferenceStore prefs;
	
	/**
	 * Creates the JackPreferencePage for provers settings.
	 */
	public PreferencePage() {
		super(GRID);
		setDescription("Preferences for the Coq proof assistant");

	}
	/**
	 * Creates the field editors. Field editors are abstractions of
	 * the common GUI blocks needed to manipulate various types
	 * of preferences. Each field editor knows how to save and
	 * restore itself.
	 */
	public void createFieldEditors() {
		
		addField(new BooleanFieldEditor(PreferencePage.COQ_MUSTPROVEALL_LIGHT, 
				"In light mode, this plugin must prove already proven lemmas.",  
				getFieldEditorParent()));
		addField(new BooleanFieldEditor(PreferencePage.COQ_MUSTPROVEALL_TOUGH, 
				"In tough mode, this plugin must prove already proven lemmas.",  
				getFieldEditorParent()));
		addField(
				new FileFieldEditor(
					PreferencePage.COQ_SEMIAUTO_LOC,
					"Location of the tactics for the semi-auto mode:",
					false,
					getFieldEditorParent()){
					public boolean checkState() {
						return true;
					}
				});
//		addField(new BooleanFieldEditor(PreferencePage.COQ_USECUSTOMCOQ, 
//				"Use custom Coq tactics (elimor, elimand...).",  
//				getFieldEditorParent()));
		addField(new BooleanFieldEditor(PreferencePage.COQ_PRETTYPRINTER, 
				"Use CoqTop pretty printing facilities.",  
				getFieldEditorParent()));
//		addField(new BooleanFieldEditor(PreferencePage.COQ_DUMBSTYLEPREL, 
//				"Use Coq uncompiled prelude in interactive mode.",  
//				getFieldEditorParent()));
	}

	public void init(IWorkbench workbench) {
		
	}
	
	public static void setDefault(IPreferenceStore store) {
		prefs = store;
		store.setDefault(COQ_MUSTPROVEALL_LIGHT, false);
		store.setDefault(COQ_MUSTPROVEALL_TOUGH, false);
		store.setDefault(COQ_USECUSTOMCOQ, false);
		store.setDefault(COQ_DUMBSTYLEPREL, false);
		store.setDefault(COQ_PRETTYPRINTER, false);
		store.setDefault(COQ_SEMIAUTO_LOC, "semiAutoTactics.v");
	}
//	public static String getCoqIde() {
//		return fr.inria.everest.coq.editor.PreferencePage.getCoqIde();
//	}
//	/**
//	 * @return
//	 */
//	public static String getCoqtopExe() {
//		return fr.inria.everest.coq.editor.PreferencePage.getCoqTop();
//	}
//	public static int getCoqGraceTime() {
//		return fr.inria.everest.coq.editor.PreferencePage.getCoqGraceTime();
//	}
	
	
	public static String getCoqSemiAuto() {
		return prefs.getString(COQ_SEMIAUTO_LOC);
	}

	/**
	 * @param b
	 * @return
	 */
	public static boolean getCoqMustProveAllLight() {
		return prefs.getBoolean(COQ_MUSTPROVEALL_LIGHT);
	}
	/**
	 * @param b
	 * @return
	 */
	public static boolean getCoqMustProveAllTough() {
		return prefs.getBoolean(COQ_MUSTPROVEALL_TOUGH);
	}
	public static boolean getCoqPrettyPrint() {
		return prefs.getBoolean(COQ_PRETTYPRINTER);
	}
	public static boolean getCoqUseDumbStylePrelude() {
		return prefs.getBoolean(COQ_DUMBSTYLEPREL);
	}
	public static boolean getCoqUseCustomTacs() {
		return prefs.getBoolean(COQ_USECUSTOMCOQ);
	}
	
	
	protected IPreferenceStore doGetPreferenceStore() {
		return prefs;
	}

}
