package beetlzplugin.runner;

import java.util.ArrayList;
import java.util.List;

import main.Beetlz;

import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.ProjectScope;
import org.eclipse.core.runtime.preferences.IScopeContext;
import org.eclipse.core.runtime.preferences.InstanceScope;
import org.eclipse.jface.preference.IPreferenceStore;
import org.eclipse.ui.preferences.ScopedPreferenceStore;

import beetlzplugin.Activator;
import beetlzplugin.preferences.PreferenceConstants;
import beetlzplugin.preferences.PreferenceInitializer;

public class UserSettings {

  /** User option. */
  private final boolean useJml;
  /** User option. */
  private final boolean useJava;
  /** User option. */
  private final boolean printError;
  /** User option. */
  private final boolean printWarning;
  /** User option. */
  private final boolean verbose;
  /** User option. */
  private final boolean pureBon;
  /** User option. */
  private final boolean nullCheck;
  /** User option. */
  private final boolean useBasics;
  /** User option. */
  private final String source;
  /** User option. */
  private final String fileName;
  /** User option. */
  private final String userFile;

  public UserSettings(IProject project) {
    final IPreferenceStore store = getAppropriatePreferenceStore(project);
    fileName = store.getString(PreferenceConstants.SPEC_PATH);
    userFile = store.getString(PreferenceConstants.USER_SETTING_PATH);
    
    useJml = store.getBoolean(PreferenceConstants.USE_JML_OPTION);
    useJava = store.getBoolean(PreferenceConstants.USE_JAVA_OPTION);
    printError = store.getBoolean(PreferenceConstants.PRINT_ERROR_OPTION);
    printWarning = store.getBoolean(PreferenceConstants.PRINT_WARNING_OPTION);
    verbose = store.getBoolean(PreferenceConstants.VERBOSE_OPTION);
    pureBon = store.getBoolean(PreferenceConstants.PURE_BON);
    nullCheck = store.getBoolean(PreferenceConstants.NULL_CHECK_OPTION);
    useBasics = store.getBoolean(PreferenceConstants.USE_BASICS_OPTION);
    source = store.getString(PreferenceConstants.SOURCE_OPTION);
  }
  
  public boolean isValid() {
    //TODO proper checking of settings...
    return true;
  }

  public String getSpecsPath() {
    return fileName;
  }
  
  /**
   * Get options the user selected on preference page and ask again
   * with gui.
   * @param args arguments list to fill in
   * @return successful and continue?
   */
  public List<String> getUserOptionsAsArgs() {
    List<String> args = new ArrayList<String>();

    if (userFile != null && !userFile.trim().isEmpty()) {
      args.add(Beetlz.USERSET_OPTION); //$NON-NLS-1$
      args.add(userFile);
    }

    String builtInSpecsPath = PreferenceInitializer.attemptToGetJMLSpecsPath();
    if (!fileName.equals(builtInSpecsPath)) {
      args.add(Beetlz.SPECS_OPTION);
      args.add(fileName);
    }

    if (!useJml) args.add(Beetlz.NO_JML_OPTION);
    if (!useJava) args.add(Beetlz.NO_JAVA_OPTION);
    if (!printError) args.add(Beetlz.NO_ERROR_OPTION);
    if (!printWarning) args.add(Beetlz.NO_WARNING_OPTION);
    if (verbose) args.add(Beetlz.VERBOSE_OPTION);
    if (pureBon) args.add(Beetlz.PUREBON_OPTION);
    if (!nullCheck) args.add(Beetlz.NON_NULL_OPTION);
    if (!useBasics) args.add(Beetlz.NO_BASICS_OPTION);
    if (source.equals("java")) { //$NON-NLS-1$
      args.add(Beetlz.SOURCE_OPTION);
      args.add("java"); //$NON-NLS-1$
    } else if (source.equals("bon")) { //$NON-NLS-1$
      args.add(Beetlz.SOURCE_OPTION);
      args.add("bon"); //$NON-NLS-1$
    } else if (source.equals("both")) {
      args.add(Beetlz.SOURCE_OPTION);
      args.add("both"); //$NON-NLS-1$
    }

    return args;
  }

  public static IPreferenceStore getAppropriatePreferenceStore(final IProject project) {
    IPreferenceStore projectPrefs = getProjectPreferenceStore(project);
    boolean projectSpecificEnabled = projectPrefs.getBoolean(PreferenceConstants.USE_PROJECT_SPECIFIC);
    if (projectSpecificEnabled) {
      return projectPrefs;
    } else {
      return getWorkspacePreferenceStore();
    }
  }
  
  private static IPreferenceStore getProjectPreferenceStore(final IProject project) {
    ProjectScope projectScope = new ProjectScope(project);
    ScopedPreferenceStore store = new ScopedPreferenceStore(new ProjectScope(project), Activator.PLUGIN_ID);
    store.setSearchContexts(new IScopeContext[] { projectScope });

    return store;
  }
  
  private static IPreferenceStore getWorkspacePreferenceStore() {
    InstanceScope instanceScope = new InstanceScope();
    ScopedPreferenceStore store = new ScopedPreferenceStore(instanceScope, Activator.PLUGIN_ID);
    store.setSearchContexts(new IScopeContext[] { instanceScope });

    return store;
  }
  
  
}
