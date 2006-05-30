package bPlugin;

import jml2b.exceptions.LanguageException;
import jml2b.formula.DeclPureMethodForm;
import jml2b.languages.ITranslatable;
import jml2b.languages.ITranslationResult;

public class BDeclPureMethodForm extends DeclPureMethodForm implements ITranslatable {

	/**
	 * 
	 */
	private static final long serialVersionUID = 1L;

	String lang;
	
	public BDeclPureMethodForm(String lang, DeclPureMethodForm form) {
		super(form);
		this.lang = lang;
	}
	
	public ITranslationResult toLang(int indent) throws LanguageException {
		return null;//TODO
	}

}
