package prover.gui.preference;

import org.eclipse.jface.preference.IPreferenceStore;
import org.eclipse.jface.preference.PreferenceNode;

/**
 * The preference node is used to wrap up the preference pages
 * and add them dynamically to Eclipse's preference pages. 
 * @author J. Charles
 */
public class ProverPreferenceNode extends PreferenceNode {
	/** the language regarding the node  */
	private String fLanguage;
	/** the current preference store */
	private IPreferenceStore fPrefs;
	/** the page to wrap up */
	private ProverPreferencePage fPage;
	
	
	/**
	 * Create a new preference node as well as an internal preference
	 * page inside of it.
	 * @param language the language to have a preference page for
	 * @param prefs the current preference store
	 */
	public ProverPreferenceNode(String language, IPreferenceStore prefs) {
		super(language + "Page");
		fLanguage = language;
		fPrefs = prefs;
		fPage = new ProverPreferencePage(language);
		fPage.setDefault(prefs);
		setPage(fPage);
	}
	
	/*
	 *  (non-Javadoc)
	 * @see org.eclipse.jface.preference.IPreferenceNode#createPage()
	 */
	public void createPage() {
		fPage = new ProverPreferencePage(fLanguage);
		fPage.setDefault(fPrefs);
		setPage(fPage);
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
}
