package prover.preference;

import org.eclipse.jface.preference.FieldEditor;
import org.eclipse.jface.preference.FieldEditorPreferencePage;
import org.eclipse.jface.preference.FileFieldEditor;
import org.eclipse.jface.preference.IPreferenceStore;
import org.eclipse.jface.preference.IntegerFieldEditor;
import org.eclipse.ui.IWorkbench;
import org.eclipse.ui.IWorkbenchPreferencePage;

public class ProverPreferencePage extends FieldEditorPreferencePage 
	implements IWorkbenchPreferencePage {
	private String PROVER_GRACETIME = "Editor.gracetime";
	private String PROVER_IDE = "Editor.ide";
	private String PROVER_TOP = "Editor.top";
	private String PROVER_COMP = "Editor.compiler";
	private IPreferenceStore fPrefs;
	private String fLanguage;
	private FieldEditor [] fFields = new FieldEditor[4];
	
	
	/**
	 * Creates the PreferencePage.
	 */
	public ProverPreferencePage() {
		super(GRID);
	}
	
	
	public ProverPreferencePage(String language) {
		this();
		setTitle(language);
		setDescription("Preferences for " + language);
		this.fLanguage = language;
		PROVER_GRACETIME += language;
		PROVER_IDE += language;
		PROVER_TOP += language;
		PROVER_COMP += language;
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
		fFields [2] = new IntegerFieldEditor(PROVER_GRACETIME, 
				      fLanguage + " toplevel grace time:", 
					 getFieldEditorParent(), 3);
		for (int i = 0; i < fFields.length; i++) {
			addField(fFields[i]);
		}
	}
	
	
	
	public void quit() {
		for (int i = 0; i < fFields.length; i++) {
			fFields[i].store();
		}
	}
	public void setDefault(IPreferenceStore pr) {
		fPrefs = pr; 
		fPrefs.setDefault(PROVER_GRACETIME, 10);
		fPrefs.setDefault(PROVER_IDE, "coqide");
		fPrefs.setDefault(PROVER_TOP, "coqtop");
	}
	
	
	public String getIde() {
		return fPrefs.getString(PROVER_IDE);
	}
	public String getTop() {
		return fPrefs.getString(PROVER_TOP);
	}
	public String getCompiler() {
		return fPrefs.getString(PROVER_COMP);
	}
	public int getGraceTime() {
		return fPrefs.getInt(PROVER_GRACETIME);
	}
	
	
	public void init(IWorkbench workbench) {
		
	}
	
	protected IPreferenceStore doGetPreferenceStore() {
		return fPrefs;
	}
}

