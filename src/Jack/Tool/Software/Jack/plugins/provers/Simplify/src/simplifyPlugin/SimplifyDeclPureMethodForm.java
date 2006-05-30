package simplifyPlugin;

import jml2b.exceptions.LanguageException;
import jml2b.formula.DeclPureMethodForm;
import jml2b.languages.ITranslatable;
import jml2b.languages.ITranslationResult;

public class SimplifyDeclPureMethodForm extends DeclPureMethodForm implements ITranslatable {

	/**
	 * 
	 */
	private static final long serialVersionUID = 1L;

	public SimplifyDeclPureMethodForm(DeclPureMethodForm form) {
		super(form);
	}
	
	public ITranslationResult toLang(int indent) throws LanguageException {
		SimplifyTranslationResult str1 =
			(SimplifyTranslationResult) ensures.toLang(
				"Simplify",
				indent);
		SimplifyTranslationResult str2 = new SimplifyTranslationResult();
		if (params != null)
		str2 =
			(SimplifyTranslationResult) params.toLang(
				"Simplify",
				indent);
		SimplifyTranslationResult str3 =
			(SimplifyTranslationResult) method.toLang(
				"Simplify",
				indent);
	
		SimplifyTranslationResult str = new SimplifyTranslationResult(
		                                     str1,
			str2,
			str3,
			"(FORALL ("
				+ (instanceType != null  ? "this" : "") 
				+ " "
				+ (params != null ? str2.toUniqString() : "")
				+ " "
				+ (result != null ? result : "")
				+ ") (IFF ("
				+ str3.toUniqString()
				+ " "
				+ (instanceType != null  ? "this" : "") 
				+ " "
				+ (params != null ? str2.toUniqString() : "")
				+ " "
				+ (result != null ? result : "")
				+ ") "
				+ str1.toUniqString()
			+ "))");
		str.addPredDecl("(DEFPRED ("
				+ str3.toUniqString()
				+ " "
				+ (instanceType != null  ? "a" : "") 
				+ " "
				+ (params != null ? str2.toUniqString() : "")
				+ " "
				+ (result != null ? "b" : "")
				+ "))"
				);
		return str;
	}

}
