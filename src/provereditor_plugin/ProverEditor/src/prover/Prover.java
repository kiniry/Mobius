package prover;

import java.util.Hashtable;
import java.util.Iterator;

import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IConfigurationElement;
import org.eclipse.jface.preference.IPreferenceStore;
import org.eclipse.ui.PlatformUI;

import prover.gui.editor.LimitRuleScanner;
import prover.gui.preference.ProverPreferenceNode;
import prover.plugins.AProverTranslator;
import prover.plugins.IProverTopLevel;

public class Prover {

	private static Hashtable fProverSet = new Hashtable();
	public static Prover get(String language) {
		return (Prover) fProverSet.get(language);
	}
	
	public static Prover findProverFromFile(String str) {
		Iterator iter = fProverSet.values().iterator();
		while(iter.hasNext()) {
			Prover p = (Prover)iter.next();
			if(p.extensionMatch(str))
					return p;
		}
		return null;
	}	
	
	


	private String fName;
	private String fExtension;
	private ProverPreferenceNode fPreference;
	private AProverTranslator fTranslator;
	private IProverTopLevel fTopLevelTranslator;
	
	public Prover (IPreferenceStore prefs, IConfigurationElement lang) {
		fName = lang.getAttribute("fName");
		fExtension = lang.getAttribute("fExtension");
		try {
			fTranslator = (AProverTranslator) lang.createExecutableExtension("fTranslator");
			fTopLevelTranslator = (IProverTopLevel) lang.createExecutableExtension("provertoplevel");
		} catch (CoreException e) {
			e.printStackTrace();
		}
		
		ProverPreferenceNode pn = new ProverPreferenceNode(fName, prefs);
		PlatformUI.getWorkbench().getPreferenceManager().addTo("ProverEditor.page",	pn);
		fPreference = pn;
		
		fProverSet.put(fName, this);
	}

	public String getIde() {
		return fPreference.getIde();
	}

	public String getTop() {
		return fPreference.getTop();
	}
	
	public String getCompiler() {
		return fPreference.getCompiler();
	}
	public int getGraceTime() {
		return fPreference.getGraceTime();
	}
	
	public AProverTranslator getTranslator() {
		return fTranslator;
	}
	
	public IProverTopLevel getTopLevelTranslator() {
		return fTopLevelTranslator;
	}
	
	private boolean extensionMatch(String str) {
		return str.endsWith(fExtension);
	}

	public LimitRuleScanner getRuleScanner() {	
		
		return new LimitRuleScanner(fTranslator.getFileRules());
	}
	
	
	public String getName() {
		return fName;
	}
	public String toString() {
		String res = fName + " (" + fExtension + "): " 
			+ fTranslator.toString() + ", " + fPreference.toString();
		return res;
	}

	public boolean isErrorMsg(String s) {
		return fTranslator.isErrorMsg(s);
	}

}
