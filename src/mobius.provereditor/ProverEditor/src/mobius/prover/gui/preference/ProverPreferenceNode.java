package mobius.prover.gui.preference;

import org.eclipse.jface.preference.IPreferencePage;
import org.eclipse.jface.preference.IPreferenceStore;
import org.eclipse.jface.preference.PreferenceNode;

/**
 * The preference node is used to wrap up the preference pages
 * and add them dynamically to Eclipse's preference pages.
 *  
 * @author J. Charles (julien.charles@inria.fr)
 */
public class ProverPreferenceNode extends PreferenceNode {
  /** the language regarding the node.  */
  private String fLanguage;
  /** the current preference store. */
  private IPreferenceStore fPrefs;
  /** the page to wrap up. */
  private ProverPreferencePage fPage;
  /** the dispose fix. */
  private boolean fDisposed;
  
  
  /**
   * Create a new preference node as well as an internal preference
   * page inside of it.
   * @param language the language to have a preference page for
   * @param prefs the current preference store
   */
  public ProverPreferenceNode(final String language, 
                              final IPreferenceStore prefs) {
    super(language + "Page");
    fLanguage = language;
    fPrefs = prefs;
    fPage = new ProverPreferencePage(language);
    fPage.setDefault(prefs);
    setPage(fPage);
  }
  
  /** {@inheritDoc} */
  @Override 
  public void createPage() {
    fPage = new ProverPreferencePage(fLanguage);
    fPage.setDefault(fPrefs);
    setPage(fPage);
    fDisposed = false;
  }

  /**
   * Returns the ide selected by the user
   * or the default value.
   * @return A string representing a file selected by the user
   */
  public String getIde() {
    return fPage.getIde();
  }

  /**
   * Returns the top level selected by the user
   * or a default value.
   * @return A string representing a file selected by the user
   */
  public String getTop() {
    return fPage.getTop();
  }
  
  /**
   * Returns the compiler selected by the user
   * or a default value.
   * @return A string representing a file selected by the user
   */
  public String getCompiler() {
    return fPage.getCompiler();
  }

  /**
   * Returns the grace time selected by the user
   * or the default value 10.
   * @return An integer selected by the user
   */
  public int getGraceTime() {
    return fPage.getGraceTime();
  }

  /** {@inheritDoc} */
  @Override
  public void disposeResources() {
    // ok this is a violent way to handle it... we DON'T 
    // dispose anything.
    fDisposed = true;
    //super.disposeResources();
  }
  
  /** {@inheritDoc} */
  @Override 
  public IPreferencePage getPage() {
    if (fDisposed) {
      createPage();
    }
    return super.getPage();
  }
  
}
