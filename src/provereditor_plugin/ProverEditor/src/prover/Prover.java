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

	private static Hashtable hs = new Hashtable();
	public static Prover get(String language) {
		return (Prover) hs.get(language);
	}
	
	public static Prover findProverFromFile(String str) {
		Iterator iter = hs.values().iterator();
		while(iter.hasNext()) {
			Prover p = (Prover)iter.next();
			if(p.extensionMatch(str))
					return p;
		}
		return null;
	}	
	
	


	private String name;
	private String extension;
	private ProverPreferenceNode preference;
	private AProverTranslator translator;
	private IProverTopLevel fTopLevelTranslator;
	
	public Prover (IPreferenceStore prefs, IConfigurationElement lang) {
		name = lang.getAttribute("name");
		extension = lang.getAttribute("extension");
		try {
			translator = (AProverTranslator) lang.createExecutableExtension("translator");
			fTopLevelTranslator = (IProverTopLevel) lang.createExecutableExtension("provertoplevel");
		} catch (CoreException e) {
			e.printStackTrace();
		}
		
		ProverPreferenceNode pn = new ProverPreferenceNode(name, prefs);
		PlatformUI.getWorkbench().getPreferenceManager().addTo("ProverEditor.page",	pn);
		preference = pn;
		
		hs.put(name, this);
		//System.out.println(this);
	}

	public String getIde() {
		return preference.getIde();
	}

	public String getTop() {
		return preference.getTop();
	}
	
	public String getCompiler() {
		return preference.getCompiler();
	}
	public int getGraceTime() {
		return preference.getGraceTime();
	}
	
	public AProverTranslator getTranslator() {
		return translator;
	}
	
	public IProverTopLevel getTopLevelTranslator() {
		return fTopLevelTranslator;
	}
	
	private boolean extensionMatch(String str) {
		return str.endsWith(extension);
	}

	public LimitRuleScanner getRuleScanner() {	
		
		return new LimitRuleScanner(translator.getFileRules());
	}
	
	
	public String getName() {
		return name;
	}
	public String toString() {
		String res = name + " (" + extension + "): " 
			+ translator.toString() + ", " + preference.toString();
		return res;
	}

	public boolean isErrorMsg(String s) {
		return translator.isErrorMsg(s);
	}

}
