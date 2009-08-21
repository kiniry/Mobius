package mobius.prover.gui.preference;

import mobius.prover.Prover;

import org.eclipse.jface.preference.IPreferenceStore;

/**
 * The preference node is used to wrap up the preference pages
 * and add them dynamically to Eclipse's preference pages.
 *  
 * @author J. Charles (julien.charles@inria.fr)
 */
public class AutomatedProverPreferenceNode extends AProverPreferenceNode {

  private AutomatedProverPreferencePage fPage;
  
  /**
   * Create a new preference node as well as an internal preference
   * page inside of it.
   * @param language the language to have a preference page for
   * @param prefs the current preference store
   */
  public AutomatedProverPreferenceNode(final Prover prover, 
                              final IPreferenceStore prefs) {
    super(prover, prefs);
  }

  /** {@inheritDoc}  */
  @Override
  public String getTop() {
    return fPage.getTop();
  }

  /** {@inheritDoc}  */
  @Override
  public int getGraceTime() {
    return fPage.getGraceTime();
  }
  
  /** {@inheritDoc}  */
  @Override
  public String getCompiler() {
    return null;
  }
  
  /** {@inheritDoc}  */
  @Override
  public String getIde() {
    return null;
  }

  /** {@inheritDoc}  */
  @Override
  protected IProverPreferencePage getPreferencePage(final Prover prover) {
    fPage = new AutomatedProverPreferencePage(prover);
    return fPage;
  }

}
