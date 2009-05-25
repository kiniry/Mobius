package beetlzplugin.preferences;

import org.eclipse.core.runtime.preferences.AbstractPreferenceInitializer;
import org.eclipse.jface.preference.IPreferenceStore;

import beetlzplugin.Activator;
import beetlzplugin.popup.actions.Messages;

/**
 * Class used to initialize default preference values.
 */
public class PreferenceInitializer extends AbstractPreferenceInitializer {


  /**
   * Initialise default values.
   */
  @Override
  public void initializeDefaultPreferences() {
    final IPreferenceStore store = Activator.getDefault().getPreferenceStore();
    store.setDefault(PreferenceConstants.SPEC_PATH, Messages.getString("PreferenceInitializer.pleaseEnterValidSpecPath")); //$NON-NLS-1$
    store.setDefault(PreferenceConstants.USER_SETTING_PATH, ""); //$NON-NLS-1$
    store.setDefault(PreferenceConstants.SKELETON_PATH, ""); //$NON-NLS-1$
    store.setDefault(PreferenceConstants.USE_BASICS_OPTION, true);
    store.setDefault(PreferenceConstants.PRINT_ERROR_OPTION, true);
    store.setDefault(PreferenceConstants.USE_JAVA_OPTION, true);
    store.setDefault(PreferenceConstants.USE_JML_OPTION, true);
    store.setDefault(PreferenceConstants.NULL_CHECK_OPTION, true);
    store.setDefault(PreferenceConstants.PRINT_WARNING_OPTION, true);
    store.setDefault(PreferenceConstants.PURE_BON, false);
    store.setDefault(PreferenceConstants.SOURCE_OPTION, "default"); //$NON-NLS-1$
    store.setDefault(PreferenceConstants.VERBOSE_OPTION, false);
  }

}
