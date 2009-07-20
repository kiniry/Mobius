package coqPlugin.language;

import jml2b.exceptions.LanguageException;
import jml2b.formula.MethodCallForm;
import jml2b.languages.ITranslatable;
import jml2b.languages.ITranslationResult;
import coqPlugin.CoqTranslationResult;

public class CoqMethodCallForm extends MethodCallForm implements ITranslatable{

	

	public CoqMethodCallForm(MethodCallForm f) {
		super(f);
	}

	/**
	 * 
	 */
	private static final long serialVersionUID = 1L;

	public ITranslationResult toLang(int indent) throws LanguageException {
		String prefix = "";
		String inst= "";
		String para = "";
		String loc = result;
		if(instance != null) {
			
			CoqTranslationResult ctrInst = (CoqTranslationResult)instance.toLang("Coq", 0);
			loc += " " + ctrInst.getLocalDecl();//CoqDeclPureMethodForm.removeType(ctrInst.getLocalDecl());
			
			loc = loc.trim();
			inst = " " + ctrInst.getFunPart();
			String prop =ctrInst.getPropPart();
			if(!prop.trim().equals(""))
				prefix += (prop + " -> ");
		}
		if(param != null) {
			CoqTranslationResult ctrParam = (CoqTranslationResult) param.toLang("Coq", 0);
			loc += " " + ctrParam.getLocalDecl();//CoqDeclPureMethodForm.removeType(ctrParam.getLocalDecl());
			loc = loc.trim();
			para = " " + ctrParam.getFunPart();
			String prop =ctrParam.getPropPart();
			if(!prop.trim().equals(""))
				prefix += (prop + " -> ");
		}
		return new CoqTranslationResult(loc, 
				prefix + m.toLang("Coq", 0) +
				inst + para +
				" " +  result, result);
	}

}
