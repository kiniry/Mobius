package simplifyPlugin;

import jml2b.exceptions.LanguageException;
import jml2b.formula.MethodCallForm;
import jml2b.languages.ITranslatable;
import jml2b.languages.ITranslationResult;

public class SimplifyMethodCallForm extends MethodCallForm implements ITranslatable{

	

	public SimplifyMethodCallForm(MethodCallForm f) {
		super(f);
	}

	/**
	 * 
	 */
	private static final long serialVersionUID = 1L;

	public ITranslationResult toLang(int indent) throws LanguageException {
		SimplifyTranslationResult str1 = new SimplifyTranslationResult();
		if (instance != null)
			str1 =
			(SimplifyTranslationResult) instance.toLang(
				"Simplify",
				indent);
		SimplifyTranslationResult str2 = new SimplifyTranslationResult();
		if (param != null)
		str2 =
			(SimplifyTranslationResult) param.toLang(
				"Simplify",
				indent);
		SimplifyTranslationResult str3 =
			(SimplifyTranslationResult) m.toLang(
				"Simplify",
				indent);
	
		return new SimplifyTranslationResult(
			str1,
			str2,
			str3,
			"("
				+ str3.toUniqString()
				+ " "
				+ (instance != null  ? str1.toUniqString() : "") 
				+ " "
				+ (param != null ? str2.toUniqString() : "")
				+ " "
				+ result
				+ ")",
			result);
	}

}
