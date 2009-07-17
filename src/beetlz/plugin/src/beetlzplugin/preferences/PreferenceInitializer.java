package beetlzplugin.preferences;

import java.io.IOException;
import java.net.URL;

import main.Beetlz;

import org.eclipse.core.runtime.FileLocator;
import org.eclipse.core.runtime.IPath;
import org.eclipse.core.runtime.Path;
import org.eclipse.core.runtime.Platform;
import org.eclipse.core.runtime.preferences.AbstractPreferenceInitializer;
import org.eclipse.jface.preference.IPreferenceStore;
import org.osgi.framework.Bundle;

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
    initializeDefaultPreferences(store);    
  }

  public static void initializeDefaultPreferences(IPreferenceStore store) {
    String jmlSpecPath = attemptToGetJMLSpecsPath();
    if (jmlSpecPath.equals("")) {
      store.setDefault(PreferenceConstants.SPEC_PATH, Messages.getString("PreferenceInitializer.pleaseEnterValidSpecPath")); //$NON-NLS-1$
    } else {
      store.setDefault(PreferenceConstants.SPEC_PATH, jmlSpecPath);
    }    
    store.setDefault(PreferenceConstants.USER_SETTING_PATH, ""); //$NON-NLS-1$
    store.setDefault(PreferenceConstants.SKELETON_PATH, ""); //$NON-NLS-1$
    store.setDefault(PreferenceConstants.USE_BASICS_OPTION, true);
    store.setDefault(PreferenceConstants.PRINT_ERROR_OPTION, true);
    store.setDefault(PreferenceConstants.USE_JAVA_OPTION, true);
    store.setDefault(PreferenceConstants.USE_JML_OPTION, true);
    store.setDefault(PreferenceConstants.NULL_CHECK_OPTION, true);
    store.setDefault(PreferenceConstants.PRINT_WARNING_OPTION, true);
    store.setDefault(PreferenceConstants.PURE_BON, false);
    store.setDefault(PreferenceConstants.SOURCE_OPTION, "both"); //$NON-NLS-1$
    store.setDefault(PreferenceConstants.VERBOSE_OPTION, false);
    store.setDefault(PreferenceConstants.BUILT_IN_SPEC_PATH, true);
    store.setDefault(PreferenceConstants.USE_PROJECT_SPECIFIC, false);
  }
  
  /**
   * Get a default value for the jml-specs path.
   * Use the openjml.jar specs that are included with the Beetlz plugin.
   * @return a path to the built-in jml specs, if possible.
   */
  public static String attemptToGetJMLSpecsPath() {
    
    Bundle bundle = Platform.getBundle(Beetlz.PLUGIN_ID);
    
    IPath p = new Path(Beetlz.JMLSPECS_PATH);
    URL url = FileLocator.find(bundle, p, null);

    try {
      URL resolvedURL = FileLocator.resolve(url);
      String filePath = resolvedURL.getPath();
      Path resourcePath = new Path(filePath);
      p = resourcePath.makeAbsolute();
      String s = p.toOSString();
      return s;
    } catch (IOException e) {
      //Not found.
      System.out.println("Didn't find built-in specs jar");
      return "";
    }
  }
  
}
