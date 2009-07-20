package mobius.prover.gui.preference;

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
 * 
 * @author J. Charles (julien.charles@inria.fr)
 */
public class ProverPreferencePage extends FieldEditorPreferencePage 
  implements IWorkbenchPreferencePage {

  /** the number of digits the grace time should have at most. */
  private static final int GRACE_DIGIT_NUMS = 3;
  /** the string representing the property to store the grace time. */
  private final String fProverGracetime;
  /** the string representing the property to store the ide location. */
  private final String fProverIde;
  /** the string representing the property to store the top level location. */
  private final String fProverTop;
  /** the string representing the property to store the compiler location. */
  private final String fProverComp;

  /** the current preference store. */
  private IPreferenceStore fPrefs;
  /** the current language associated with the preference page. */
  private final String fLanguage;
  
  /** the field to specify the compiler. */
  private FieldEditor fCompilerField;
  /** the field to specify the grace time. */
  private FieldEditor fGraceField;
  /** the field to specify the top level. */
  private FieldEditor fToplevField;
  /** the field to specify the ide. */
  private FieldEditor fIdeField;

  
  
  /**
   * Creates the PreferencePage.
   * @param language the language for whiche the preference page
   * have to be created
   */  
  public ProverPreferencePage(final String language) {
    super(GRID);
    fLanguage = language;
    fProverGracetime = fLanguage + "Editor.gracetime";
    fProverIde = fLanguage + "Editor.ide";
    fProverTop = fLanguage + "Editor.top";
    fProverComp = fLanguage + "Editor.compiler";
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
    fIdeField = new FileFieldEditor(
        fProverIde,
        fLanguage + " ide path:",
        true,
        getFieldEditorParent()) {
      public boolean checkState() {
        return true;
      }
    }; 
    fToplevField =    new FileFieldEditor(
           fProverTop,
           fLanguage + " toplevel path:",
           true,
           getFieldEditorParent());
    fCompilerField = new FileFieldEditor(
           fProverComp,
           fLanguage + " compiler path:",
           true,
           getFieldEditorParent());
    fGraceField = new IntegerFieldEditor(fProverGracetime, 
              fLanguage + " toplevel grace time:", 
           getFieldEditorParent(), GRACE_DIGIT_NUMS);
    addField(fIdeField);
    addField(fToplevField);
    addField(fCompilerField);
    addField(fGraceField);
  }
  
  /**
   * Sets the preference store.
   * @param prefs the new preference store.
   */
  public void setDefault(final IPreferenceStore prefs) {
    fPrefs = prefs; 
    fPrefs.setDefault(fProverGracetime, 10);
    fPrefs.setDefault(fProverIde, "ide");
    fPrefs.setDefault(fProverTop, "top");
    fPrefs.setDefault(fProverComp, "comp");
  }
  
  
  /**
   * Returns the ide selected by the value
   * or the default value.
   * @return A string representing a file selected by the user
   */
  public String getIde() {
    return fPrefs.getString(fProverIde);
  }
  
  /**
   * Returns the top level selected by the user
   * or a default value.
   * @return A string representing a file selected by the user
   */
  public String getTop() {
    return fPrefs.getString(fProverTop);
  }
  
  /**
   * Returns the compiler selected by the user
   * or a default value.
   * @return A string representing a file selected by the user
   */
  public String getCompiler() {
    return fPrefs.getString(fProverComp);
  }
  
  /**
   * Returns the grace time selected by the user
   * or the default value 10.
   * @return An integer selected by the user
   */
  public int getGraceTime() {
    return fPrefs.getInt(fProverGracetime);
  }
  
  /** {@inheritDoc} */
  public void init(final IWorkbench workbench) { }
  
  /** {@inheritDoc} */
  @Override
  protected IPreferenceStore doGetPreferenceStore() {
    return fPrefs;
  }
}

