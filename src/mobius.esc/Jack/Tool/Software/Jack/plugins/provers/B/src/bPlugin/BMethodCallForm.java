package bPlugin;

import jml2b.exceptions.LanguageException;
import jml2b.formula.MethodCallForm;
import jml2b.languages.ITranslatable;
import jml2b.languages.ITranslationResult;

public class BMethodCallForm extends MethodCallForm implements ITranslatable{

	String lang;

	public BMethodCallForm(String lang, MethodCallForm f) {
		super(f);
		this.lang = lang;
	}

	/**
	 * 
	 */
	private static final long serialVersionUID = 1L;

	public ITranslationResult toLang(int indent) throws LanguageException {
		return null; //TODO
	}

}
