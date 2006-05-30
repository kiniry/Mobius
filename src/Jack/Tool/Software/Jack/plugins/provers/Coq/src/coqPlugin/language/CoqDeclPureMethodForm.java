package coqPlugin.language;

import jml2b.exceptions.LanguageException;
import jml2b.formula.DeclPureMethodForm;
import jml2b.formula.TTypeForm;
import jml2b.languages.ITranslatable;
import jml2b.languages.ITranslationResult;
import coqPlugin.CoqTranslationResult;

public class CoqDeclPureMethodForm extends DeclPureMethodForm implements ITranslatable {

	/**
	 * 
	 */
	private static final long serialVersionUID = 1L;

	public CoqDeclPureMethodForm(DeclPureMethodForm form) {
		super(form);
	}
	
	public ITranslationResult toLang(int indent) throws LanguageException {
		//String i = CoqLanguage.newName("i");
		TTypeForm ct = (TTypeForm)this.instanceType;
		String strParams = ((params == null) ?"" : (" "+ new CoqTranslationResult(params)));
		strParams = removeType(strParams);
		
		return new CoqTranslationResult("", method.toLang("Coq", 0).toString(),
				"Definition " +
				method.toLang("Coq", 0) + " := fun " +
				((ct == null) ?"" : ("this")) +
				strParams +
				((result == null) ?"" : (" "+ new CoqTranslationResult(result))) +" => "	+ 
				this.ensures.toLang("Coq", 0));
	}
	
	public static String removeType(String s){
		return s.replace('(', ' ').replaceAll(":[^)]*\\)", "");
	}

}
