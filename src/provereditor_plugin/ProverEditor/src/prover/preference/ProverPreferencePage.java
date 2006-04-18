package prover.gui.preference;

import org.eclipse.jface.preference.FieldEditor;
import org.eclipse.jface.preference.FieldEditorPreferencePage;
import org.eclipse.jface.preference.FileFieldEditor;
import org.eclipse.jface.preference.IPreferenceStore;
import org.eclipse.jface.preference.IntegerFieldEditor;
import org.eclipse.ui.IWorkbench;
import org.eclipse.ui.IWorkbenchPreferencePage;

/**
 * The prover preference page. For each prover a prover preference
 * page is added, giving the properties for the grace time,
 * the ide, the top level and the compiler.
 * @author J. Charles
 */
public class ProverPreferencePage extends FieldEditorPreferencePage 
	implements IWorkbenchPreferencePage {

	/** the string representing the property to store the grace time */
	private final String PROVER_GRACETIME;
	/** the string representing the property to store the ide location */
	private final String PROVER_IDE;
	/** the string representing the property to store the top level location */
	private final String PROVER_TOP;
	/** the string representing the property to store the compiler location */
	private final String PROVER_COMP;

	/** the current preference store */
	private IPreferenceStore fPrefs;
	/** the current language associated with the preference page */
	private String fLanguage;
	/** the different fields shown in the page */
	private FieldEditor [] fFields = new FieldEditor[4];
	
	
	/**
	 * Creates the PreferencePage.
	 * @param language the language for whiche the preference page
	 * have to be created
	 */	
	public ProverPreferencePage(String language) {
		super(GRID);
		fLanguage = language;
		PROVER_GRACETIME = fLanguage + "Editor.gracetime";
		PROVER_IDE = fLanguage + "Editor.ide";
		PROVER_TOP = fLanguage + "Editor.top";
		PROVER_COMP = fLanguage + "Editor.compiler";
		setTitle(fLanguage);
		setDescription("Preferences for " + fLanguage);
	}
	
	
	/**
	 * Creates the field editors. Field editors are abstractions of
	 * the common GUI blocks needed to manipulate various types
	 * of preferences. Each field editor knows how to save and
	 * restore itself.
	 */
	public void createFieldEditors() {
		fFields [0] = new FileFieldEditor(
				PROVER_IDE,
				fLanguage + " ide path:",
				true,
				getFieldEditorParent()){
						public boolean checkState() {
							return true;
						}
					}; 
		fFields [1] = 	 new FileFieldEditor(
					 PROVER_TOP,
					 fLanguage + " toplevel path:",
					 true,
					 getFieldEditorParent());
		fFields [2] = 	 new FileFieldEditor(
				 PROVER_COMP,
				 fLanguage + " compiler path:",
				 true,
				 getFieldEditorParent());
		fFields [3] = new IntegerFieldEditor(PROVER_GRACETIME, 
				      fLanguage + " toplevel grace time:", 
					 getFieldEditorParent(), 3);
		for (int i = 0; i < fFields.length; i++) {
			addField(fFields[i]);
		}
	}
	
	/**
	 * Sets the preference store.
	 * @param prefs the new preference store.
	 */
	public void setDefault(IPreferenceStore prefs) {
		fPrefs = prefs; 
		fPrefs.setDefault(PROVER_GRACETIME, 10);
		fPrefs.setDefault(PROVER_IDE, "ide");
		fPrefs.setDefault(PROVER_TOP, "top");
		fPrefs.setDefault(PROVER_COMP, "comp");
	}
	
	
	/**
	 * Returns the ide selected by the value
	 * or the default value.
	 * @return A string representing a file selected by the user
	 */
	public String getIde() {
		return fPrefs.getString(PROVER_IDE);
	}
	
	/**
	 * Returns the top level selected by the user
	 * or a default value.
	 * @return A string representing a file selected by the user
	 */
	public String getTop() {
		return fPrefs.getString(PROVER_TOP);
	}
	
	/**
	 * Returns the compiler selected by the user
	 * or a default value.
	 * @return A string representing a file selected by the user
	 */
	public String getCompiler() {
		return fPrefs.getString(PROVER_COMP);
	}
	
	/**
	 * Returns the grace time selected by the user
	 * or the default value 10.
	 * @return An integer selected by the user
	 */
	public int getGraceTime() {
		return fPrefs.getInt(PROVER_GRACETIME);
	}
	
	/*
	 *  (non-Javadoc)
	 * @see org.eclipse.ui.IWorkbenchPreferencePage#init(org.eclipse.ui.IWorkbench)
	 */
	public void init(IWorkbench workbench) { }
	
	/*
	 *  (non-Javadoc)
	 * @see org.eclipse.jface.preference.PreferencePage#doGetPreferenceStore()
	 */
	protected IPreferenceStore doGetPreferenceStore() {
		return fPrefs;
	}
}

