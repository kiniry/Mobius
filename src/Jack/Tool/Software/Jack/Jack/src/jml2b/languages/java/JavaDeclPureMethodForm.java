/*
 * Created on Sep 14, 2005
 *
 * To change the template for this generated file go to
 * Window&gt;Preferences&gt;Java&gt;Code Generation&gt;Code and Comments
 */
package jml2b.languages.java;

import jml2b.exceptions.LanguageException;
import jml2b.formula.DeclPureMethodForm;
import jml2b.languages.ITranslatable;
import jml2b.languages.ITranslationResult;

public class JavaDeclPureMethodForm extends DeclPureMethodForm implements ITranslatable {

	/**
	 * 
	 */
	private static final long serialVersionUID = 1L;

	JavaDeclPureMethodForm(DeclPureMethodForm f) {
		super(f);
	}

	public ITranslationResult toLang(int indent) throws LanguageException {
		String res = ""; 
		if (instanceType != null)
			res = (JavaTranslationResult) instanceType.toLang("Java", indent + 3)  + ".";
		res += (JavaTranslationResult) method.toLang("Java", indent + 3) + "(";
		if (params != null)	
		res += (JavaTranslationResult) params.toLang("Java", indent + 3);
		if (result != null)	
			res += (params != null ? "," : "") + result;
		res += ") {";
		return new JavaTranslationResult(res + (JavaTranslationResult) ensures.toLang("Java", indent + 3)+"}" , 0);
	}

}
