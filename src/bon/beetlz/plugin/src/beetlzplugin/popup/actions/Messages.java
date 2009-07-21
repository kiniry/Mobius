package beetlzplugin.popup.actions;

import java.util.Locale;
import java.util.MissingResourceException;
import java.util.ResourceBundle;

/**
 * Localisation class, from Eclipse template.
 */
public class Messages {
  private static final String BUNDLE_NAME =
    "beetlzplugin.popup.actions.messages"; //$NON-NLS-1$

  private static final ResourceBundle RESOURCE_BUNDLE = ResourceBundle
      .getBundle(BUNDLE_NAME, new Locale(System.getProperty("user.language"))); //$NON-NLS-1$

  private Messages() {
  }

  public static String getString(String key) {
    try {
      return RESOURCE_BUNDLE.getString(key);
    } catch (MissingResourceException e) {
      return '!' + key + '!';
    }
  }
}
