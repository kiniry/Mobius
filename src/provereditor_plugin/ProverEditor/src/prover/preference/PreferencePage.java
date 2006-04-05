package prover.preference;

import org.eclipse.jface.preference.BooleanFieldEditor;
import org.eclipse.jface.preference.FieldEditor;
import org.eclipse.jface.preference.FieldEditorPreferencePage;
import org.eclipse.jface.preference.IPreferenceStore;
import org.eclipse.ui.IWorkbench;
import org.eclipse.ui.IWorkbenchPreferencePage;

public class PreferencePage extends FieldEditorPreferencePage 
	implements IWorkbenchPreferencePage {
	private static final String PROVER_UNICODE = "ProverEditor.unicode";
	private static PreferencePage curr;
	private static IPreferenceStore prefs;
	/**
	 * Creates the PreferencePage.
	 */
	public PreferencePage() {
		super(GRID);
		curr = this;
		setDescription("Preferences for the TopLevel proof assistant");
	
	}
	FieldEditor [] fe = new FieldEditor[1];
	/**
	 * Creates the field editors. Field editors are abstractions of
	 * the common GUI blocks needed to manipulate various types
	 * of preferences. Each field editor knows how to save and
	 * restore itself.
	 */
	public void createFieldEditors() {

		fe [0] = new BooleanFieldEditor(PROVER_UNICODE, 
				 "Use unicode special characters", 
				 getFieldEditorParent());
		for (int i = 0; i < fe.length; i++) {
			addField(fe[i]);
		}
	}
	
	public static PreferencePage getDefault() {
		return curr;
	}
	
	
	public void quit() {
		for (int i = 0; i < fe.length; i++) {
			fe[i].store();
		}
	}
	public static void setDefault(IPreferenceStore pr) {
		prefs = pr; 
		prefs.setDefault(PROVER_UNICODE, false);
	}

	public static boolean getProverIsUnicode() {
		return prefs.getBoolean(PROVER_UNICODE);
	}
	
	
	public void init(IWorkbench workbench) {
		
	}
	
	protected IPreferenceStore doGetPreferenceStore() {
		return prefs;
	}
}

