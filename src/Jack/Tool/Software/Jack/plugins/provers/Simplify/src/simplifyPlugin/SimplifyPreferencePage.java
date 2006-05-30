//******************************************************************************
/* Copyright (c) 2003 INRIA. All Rights Reserved.
 /*------------------------------------------------------------------------------
 /* Name: 
 /*
 /*******************************************************************************
 /* Warnings/Remarks:
 /******************************************************************************/

package simplifyPlugin;

import org.eclipse.jface.preference.FieldEditorPreferencePage;
import org.eclipse.jface.preference.FileFieldEditor;
import org.eclipse.jface.preference.IPreferenceStore;
import org.eclipse.jface.preference.IntegerFieldEditor;
import org.eclipse.jface.preference.StringFieldEditor;
import org.eclipse.ui.IWorkbench;
import org.eclipse.ui.IWorkbenchPreferencePage;

/**
 * @author L. Burdy
 */
public class SimplifyPreferencePage extends FieldEditorPreferencePage implements IWorkbenchPreferencePage {

	public static final String SIMPLIFY_EXE = "simplifyexe";
	public static final String SIMPLIFY_EXE_OPTIONS = "simplifyexeOptions";
	public static final String PO_PER_FILE = "poperfile";

	/**
	 * Creates the JackPreferencePage for provers settings.
	 */
	public SimplifyPreferencePage() {
		super(GRID);
		setPreferenceStore(SimplifyPlugin.getDefault().getPreferenceStore());
		// Soooo it doesn't work
		/* try {
			String m = Messages.getString("SimplifyPreferencePage.Preferences_for_the_simplify_prover_1"); //$NON-NLS-1$
			setDescription(m);
		}
		catch (Exception e) {*/
		setDescription("Preferences for the simplify prover");
		//}
	}
	/**
	 * Creates the field editors. Field editors are abstractions of the common
	 * GUI blocks needed to manipulate various types of preferences. Each field
	 * editor knows how to save and restore itself.
	 */
	public void createFieldEditors() {
		addField(new FileFieldEditor(SimplifyPreferencePage.SIMPLIFY_EXE, "Simplify Executable", //$NON-NLS-1$
				true, getFieldEditorParent()));
		addField(new StringFieldEditor(SimplifyPreferencePage.SIMPLIFY_EXE_OPTIONS, "Simplify exe options",
				getFieldEditorParent()));
		addField(new IntegerFieldEditor(SimplifyPreferencePage.PO_PER_FILE, 
				"Number of proof obligations per output files", //$NON-NLS-1$
				getFieldEditorParent()) {
			public boolean isValid() {
				return getIntValue() != 0;
			}
			public String getErrorMessage() {
				return Messages.getString("SimplifyPreferencePage.The_value_must_not_be_zero._2"); //$NON-NLS-1$
			}
		});
	}

	public void init(IWorkbench workbench) {

	}
	public static int getPoPerFile() {
		IPreferenceStore prefs =
			SimplifyPlugin.getDefault().getPreferenceStore();
		return prefs.getInt(PO_PER_FILE);
	}
	/**
	 * Returns the simplify exe.
	 */
	public static String getSimplifyExe() {
		IPreferenceStore prefs =
			SimplifyPlugin.getDefault().getPreferenceStore();
		return prefs.getString(SIMPLIFY_EXE) + " " + prefs.getString(SIMPLIFY_EXE_OPTIONS);
	}

}