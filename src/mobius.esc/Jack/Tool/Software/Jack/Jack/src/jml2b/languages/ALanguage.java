package jml2b.languages;

import jml2b.exceptions.LanguageException;
import jpov.structure.VirtualFormula;


/**
 * Basic implementation of the interface ILanguage
 * @author jcharles
 *
 */
public abstract class ALanguage implements ILanguage {
	public String[] displayHyp(VirtualFormula[] f) throws LanguageException {
		String [] tab = new String[f.length];
		for(int i = 0; i < tab.length; i++) {
			tab [i] = f[i].getF().toLang(getName(), 0).toUniqString();
		}
		return tab;
	}
}
