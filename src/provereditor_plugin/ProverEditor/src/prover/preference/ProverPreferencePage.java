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
	private IPreferenceStore prefs;
	private String language;
	
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
		this.language = language;
		PROVER_GRACETIME += language;
		PROVER_IDE += language;
		PROVER_TOP += language;
	}
	FieldEditor [] fe = new FieldEditor[3];
	/**
	 * Creates the field editors. Field editors are abstractions of
	 * the common GUI blocks needed to manipulate various types
	 * of preferences. Each field editor knows how to save and
	 * restore itself.
	 */
	public void createFieldEditors() {
		fe [0] = new FileFieldEditor(
				PROVER_IDE,
				language + " ide path:",
				true,
				getFieldEditorParent()){
						public boolean checkState() {
							return true;
						}
					}; 
		fe [1] = 	 new FileFieldEditor(
					 PROVER_TOP,
					 language + " toplevel path:",
					 true,
					 getFieldEditorParent());
		fe [2] = new IntegerFieldEditor(PROVER_GRACETIME, 
				      language + " toplevel grace time:", 
					 getFieldEditorParent(), 3);
		for (int i = 0; i < fe.length; i++) {
			addField(fe[i]);
		}
	}
	
	
	
	public void quit() {
		for (int i = 0; i < fe.length; i++) {
			fe[i].store();
		}
	}
	public void setDefault(IPreferenceStore pr) {
		prefs = pr; 
		prefs.setDefault(PROVER_GRACETIME, 10);
		prefs.setDefault(PROVER_IDE, "coqide");
		prefs.setDefault(PROVER_TOP, "coqtop");
	}
	
	
	public String getIde() {
		return prefs.getString(PROVER_IDE);

	}
	public String getTop() {
		return prefs.getString(PROVER_TOP);
	}

	
	
	public int getGraceTime() {
		return prefs.getInt(PROVER_GRACETIME);
	}
	public void init(IWorkbench workbench) {
		
	}
	
	protected IPreferenceStore doGetPreferenceStore() {
		return prefs;
	}
}

