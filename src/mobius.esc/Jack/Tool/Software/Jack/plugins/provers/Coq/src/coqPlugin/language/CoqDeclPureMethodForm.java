package coqPlugin.language;

import jml2b.exceptions.LanguageException;
import jml2b.formula.DeclPureMethodForm;
import jml2b.formula.QuantifiedVarForm;
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
		TTypeForm ct = (TTypeForm)instanceType;
		String this_type = pureVariableDecl("this", ct).getLocalDecl();

		String res_str = pureVariableDecl(result, resultType).getLocalDecl();
	
		String strParams = ((params == null) ?"" : (" "+ paramDecl(params)));
		//strParams = removeType(strParams);
		String strMethodName = method.toLang("Coq", 0).toString();
		return new CoqTranslationResult("", strMethodName,
				"Definition " +
				strMethodName + " := fun " +
				this_type + 
				strParams + "  " +
				res_str +" => "	+ 
				this.ensures.toLang("Coq", 0));
	}
	
	private static String paramDecl(QuantifiedVarForm params) throws LanguageException {
		String res = "";
		while(params != null) {
			res += " "+ pureVariableDecl(params.getVar().toLang("Coq", 0).toString(),
					(TTypeForm)params.getType()).getLocalDecl();
			params = params.getNext();
		} 
		
		return res;
	}

	/**
	 * @deprecated do not use it
	 */
	public static String removeType(String s){
		return s.replace('(', ' ').replaceAll(":[^)]*\\)", "");
	}
	
	public static CoqTranslationResult pureVariableDecl(String name, TTypeForm ttf) throws LanguageException{
		CoqTranslationResult res = new CoqTranslationResult();
		if(ttf == null) return res;
		if(name != null)  {
			if(ttf.isNative()) {
				res = CoqTranslationResult.buildFromLocal(" ("+ new CoqTranslationResult(name) + ": " + ttf.toLang("Coq", 0)+ ")");
			}
			else if (ttf.isRef()) {
				res =    CoqTranslationResult.buildFromLocal(" ("+ new CoqTranslationResult(name) + ": " + 
									CoqType.Reference + ")");
			}
			else {
				CoqType tmp = CoqType.getType(ttf);
				res = CoqTranslationResult.buildFromLocal(
						" ("+ new CoqTranslationResult(name) + ": " + 
					tmp.toString() + ")");
			}
		}
		return res;
	}

}
