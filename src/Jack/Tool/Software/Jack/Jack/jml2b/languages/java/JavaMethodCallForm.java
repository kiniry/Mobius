/*
 * Created on Sep 14, 2005
 *
 * To change the template for this generated file go to
 * Window&gt;Preferences&gt;Java&gt;Code Generation&gt;Code and Comments
 */
package jml2b.languages.java;

import jml2b.exceptions.LanguageException;
import jml2b.formula.MethodCallForm;
import jml2b.languages.ITranslatable;
import jml2b.languages.ITranslationResult;

public class JavaMethodCallForm extends MethodCallForm implements ITranslatable {

	/**
	 * 
	 */
	private static final long serialVersionUID = 1L;

	JavaMethodCallForm(MethodCallForm f) {
		super(f);
	}

	public ITranslationResult toLang(int indent) throws LanguageException {
	String res =  result + " with property ";
		if (instance != null)
			res += (JavaTranslationResult) instance.toLang("Java", indent + 3) + ".";
		res += (JavaTranslationResult) this.m.toLang("Java", indent) + "(";
		if (param != null)
			res += (JavaTranslationResult) param.toLang("Java", indent + 3) + ",";
		return new JavaTranslationResult(res + result + ")", 0);
	}

}
