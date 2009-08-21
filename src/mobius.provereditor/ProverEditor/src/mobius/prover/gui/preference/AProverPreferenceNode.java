package mobius.prover.gui.preference;

import mobius.prover.Prover;

import org.eclipse.jface.preference.IPreferencePage;
import org.eclipse.jface.preference.IPreferenceStore;
import org.eclipse.jface.preference.PreferenceNode;

public abstract class AProverPreferenceNode extends PreferenceNode {
  /** the language regarding the node.  */
  private Prover fProver;
  /** the current preference store. */
  private IPreferenceStore fPrefs;
  /** the page to wrap up. */
  private  IProverPreferencePage fPage;
  /** the dispose fix. */
  private boolean fDisposed;
  
  
  /**
   * Create a new preference node as well as an internal preference
   * page inside of it.
   * @param prover the language to have a preference page for
   * @param prefs the current preference store
   */
  public AProverPreferenceNode(final Prover prover, 
                              final IPreferenceStore prefs) {
    super(prover.getName() + "Page");
    fProver = prover;
    fPrefs = prefs;
    createPage();
  }
  
  /** {@inheritDoc} */
  @Override 
  public void createPage() {
    fPage = getPreferencePage(fProver);
    fPage.setDefault(fPrefs);
    setPage(fPage);
    fDisposed = false;
  }

  protected abstract IProverPreferencePage getPreferencePage(Prover prover);

  /**
   * Returns the ide selected by the user
   * or the default value.
   * @return A string representing a file selected by the user
   */
  public abstract String getIde();

  /**
   * Returns the top level selected by the user
   * or a default value.
   * @return A string representing a file selected by the user
   */
  public abstract String getTop();
  
  /**
   * Returns the compiler selected by the user
   * or a default value.
   * @return A string representing a file selected by the user
   */
  public abstract String getCompiler();

  /**
   * Returns the grace time selected by the user
   * or the default value 10.
   * @return An integer selected by the user
   */
  public abstract int getGraceTime();

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

  public static interface IProverPreferencePage extends IPreferencePage {
    void setDefault(final IPreferenceStore prefs);
  }
}
