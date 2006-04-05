package prover.preference;

import org.eclipse.jface.preference.IPreferenceStore;
import org.eclipse.jface.preference.PreferenceNode;


public class ProverPreferenceNode extends PreferenceNode {
	private String language;
	private IPreferenceStore prefs;
	private ProverPreferencePage ppp;
	public ProverPreferenceNode(String language, IPreferenceStore prefs) {
		super(language + "Page");
		this.language = language;
		this.prefs = prefs;
		ppp = new ProverPreferencePage(language);
		ppp.setDefault(prefs);
		setPage(ppp);
	}
	
	  public void createPage() {
		  ppp = new ProverPreferencePage(language);
		  ppp.setDefault(prefs);
		  setPage(ppp);
	  }

	public String getIde() {
		return ppp.getIde();
	}

	public String getTop() {
		return ppp.getTop();
	}

	public int getGraceTime() {
		return ppp.getGraceTime();
	}
}
