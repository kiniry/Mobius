package mobius.prover.gui.preference;

import mobius.prover.Prover;
import mobius.prover.gui.preference.AProverPreferenceNode.IProverPreferencePage;

import org.eclipse.jface.preference.ComboFieldEditor;
import org.eclipse.jface.preference.FieldEditor;
import org.eclipse.jface.preference.FieldEditorPreferencePage;
import org.eclipse.jface.preference.IPreferenceStore;
import org.eclipse.jface.preference.IntegerFieldEditor;
import org.eclipse.ui.IWorkbench;
import org.eclipse.ui.IWorkbenchPreferencePage;

import pluginlib.Utils.ProverPath;

/**
 * The prover preference page. For each prover a prover preference
 * page is added, giving the properties for the grace time,
 * the ide, the top level and the compiler.
 * 
 * @author J. Charles (julien.charles@inria.fr)
 */
public class AutomatedProverPreferencePage extends FieldEditorPreferencePage 
  implements IWorkbenchPreferencePage, IProverPreferencePage {

  /** the number of digits the grace time should have at most. */
  private static final int GRACE_DIGIT_NUMS = 3;
  /** the string representing the property to store the grace time. */
  private final String fProverGracetime;

  /** the string representing the property to store the top level location. */
  private final String fProverTop;

  /** the current preference store. */
  private IPreferenceStore fPrefs;
  /** the current prover associated with the preference page. */
  private final Prover fProver;
  
  /** the field to specify the grace time. */
  private FieldEditor fGraceField;
  /** the field to specify the top level. */
  private FieldEditor fToplevField;

  
  
  /**
   * Creates the PreferencePage.
   * @param prover the language for whiche the preference page
   * have to be created
   */  
  public AutomatedProverPreferencePage(final Prover prover) {
    super(GRID);
    fProver = prover;
    String lang = prover.getName();
    fProverGracetime = lang + "Editor.gracetime";
    fProverTop = lang + "Editor.top";
    setTitle(lang);
    setDescription("Preferences for " + lang);
  }
  
  
  /**
   * Creates the field editors. Field editors are abstractions of
   * the common GUI blocks needed to manipulate various types
   * of preferences. Each field editor knows how to save and
   * restore itself.
   */
  public void createFieldEditors() {
    String [][] values = translate(fProver.getTranslator().getBuiltInProvers());
    fToplevField =    new ComboFieldEditor(
           fProverTop,
           fProver.getName() + " executable:",
           values,
           getFieldEditorParent());
 
    fGraceField = new IntegerFieldEditor(
                     fProverGracetime, 
                     fProver.getName() + " grace time:", 
           getFieldEditorParent(), GRACE_DIGIT_NUMS);
    addField(fToplevField);
    addField(fGraceField);
  }
  
  private String[][] translate(ProverPath[] builtInProvers) {
    String [][] res = new String [builtInProvers.length][]; 
    for (int i = 0; i < builtInProvers.length; i++) {
      ProverPath pp = builtInProvers[i];
      res[i] = new String [] {pp.getName(), pp.getPath()};
    }
    return res;
  }


  /**
   * Sets the preference store.
   * @param prefs the new preference store.
   */
  public void setDefault(final IPreferenceStore prefs) {
    fPrefs = prefs; 
    fPrefs.setDefault(fProverGracetime, 10);
    fPrefs.setDefault(fProverTop, "top");
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

