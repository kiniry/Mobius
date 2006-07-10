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
		String this_type = "";
		if (ct != null) {
			if(ct.isNative()) {
				this_type = " (this : " + ct.toLang("Coq", 0).toString() + ")";
			}
			else {
				this_type = " (this : " + CoqType.Reference + ")";
			}
		}
		String res_str = "";
		if(result != null)  {
			if(resultType.isNative()) {
				res_str = " ("+ new CoqTranslationResult(result) + ": " + resultType.toLang("Coq", 0)+ ")";
			}
			else if (resultType.isRef()) {
				res_str =  " ("+ new CoqTranslationResult(result) + ": " + 
									CoqType.Reference + ")";
			}
			else {
				res_str =  " ("+ new CoqTranslationResult(result) + ": " + 
					resultType.toLang("Coq", 0) + ")";
			}
		}
		
		String strParams = ((params == null) ?"" : (" "+ new CoqTranslationResult(params)));
		//strParams = removeType(strParams);
		String strMethodName = method.toLang("Coq", 0).toString();
		return new CoqTranslationResult("", strMethodName,
				"Definition " +
				strMethodName + " := fun" +
				this_type +
				strParams +
				res_str +" => "	+ 
				this.ensures.toLang("Coq", 0));
	}
	
	public static String removeType(String s){
		return s.replace('(', ' ').replaceAll(":[^)]*\\)", "");
	}

}
