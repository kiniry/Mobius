package canapa.preferences;


import org.eclipse.core.runtime.preferences.AbstractPreferenceInitializer;
import org.eclipse.core.runtime.preferences.DefaultScope;
import org.osgi.service.prefs.Preferences;

/**
 * Class used to initialize default preference values.
 */
public class PreferenceInitializer extends AbstractPreferenceInitializer {

	/*
	 * (non-Javadoc)
	 * 
	 * @see org.eclipse.core.runtime.preferences.AbstractPreferenceInitializer#initializeDefaultPreferences()
	 */
	public void initializeDefaultPreferences() {
		String key = "CANAPA."+PreferenceConstants.P_SIMPLIFY_FILE;
		Preferences node = new DefaultScope().getNode(key);
		String os = System.getProperty("os.name");
		if (os == null){
			//if none found - assume mac
			node.put(key, PreferenceConstants.P_SIMPLIFY_CHOICES[2][0]);
			return;
		}
		if (os.contains("Windows")){
			node.put(key, PreferenceConstants.P_SIMPLIFY_CHOICES[0][0]);
		}
		else if (os.contains("Linux")){
			node.put(key, PreferenceConstants.P_SIMPLIFY_CHOICES[1][0]);
		}
		else {
			node.put(key, PreferenceConstants.P_SIMPLIFY_CHOICES[2][0]);
		}

	}

}
