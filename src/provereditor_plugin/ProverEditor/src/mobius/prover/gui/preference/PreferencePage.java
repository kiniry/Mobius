package mobius.prover.gui.preference;

import org.eclipse.jface.preference.BooleanFieldEditor;
import org.eclipse.jface.preference.FieldEditor;
import org.eclipse.jface.preference.FieldEditorPreferencePage;
import org.eclipse.jface.preference.IPreferenceStore;
import org.eclipse.ui.IWorkbench;
import org.eclipse.ui.IWorkbenchPreferencePage;

/**
 * The class representing the ProverEditor preference page.
 */
public class PreferencePage extends FieldEditorPreferencePage 
	implements IWorkbenchPreferencePage {
	/** the property to store the unicode preference */
	public static final String PROVER_UNICODE = "ProverEditor.unicode";
	/** the current instance of this class */
	private static PreferencePage fInstance;
	/** the current preference store */
	private static IPreferenceStore fPrefs;

	/** the different fields shown in the page */
	private FieldEditor [] fFields = new FieldEditor[1];


	/**
	 * Returns the current preference page instance, or 
	 * <code>null</code> if it doesn't exist.
	 * @return an instance of the preference page.
	 */
	public static PreferencePage getInstance() {
		return fInstance;
	}
	
	
	/**
	 * Sets the preference store.
	 * @param prefs the new preference store.
	 */
	public static void setDefault(IPreferenceStore prefs) {
		fPrefs = prefs; 
		fPrefs.setDefault(PROVER_UNICODE, false);
	}

	/**
	 * Return whether or not unicode replacements shall
	 * be used. 
	 * @return The value in the preference store
	 */
	public static boolean getProverIsUnicode() {
		return fPrefs.getBoolean(PROVER_UNICODE);
	}
	
	
	/**
	 * Creates the PreferencePage.
	 */
	public PreferencePage() {
		super(GRID);
		fInstance = this;
		setDescription("Preferences for the TopLevel proof assistant");
	
	}
	/**
	 * Creates the field editors. Field editors are abstractions of
	 * the common GUI blocks needed to manipulate various types
	 * of preferences. Each field editor knows how to save and
	 * restore itself.
	 */
	public void createFieldEditors() {

		fFields [0] = new BooleanFieldEditor(PROVER_UNICODE, 
				 "Use unicode special characters", 
				 getFieldEditorParent());
		for (int i = 0; i < fFields.length; i++) {
			addField(fFields[i]);
		}
	}
	
	
	/*
	 *  (non-Javadoc)
	 * @see org.eclipse.ui.IWorkbenchPreferencePage#init(org.eclipse.ui.IWorkbench)
	 */
	public void init(IWorkbench workbench) {}
	
			
	/*
	 *  (non-Javadoc)
	 * @see org.eclipse.jface.preference.PreferencePage#doGetPreferenceStore()
	 */
	protected IPreferenceStore doGetPreferenceStore() {
		return fPrefs;
	}
}

