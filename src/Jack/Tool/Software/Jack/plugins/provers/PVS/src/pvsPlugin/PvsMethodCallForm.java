package pvsPlugin;

import jml2b.exceptions.LanguageException;
import jml2b.formula.MethodCallForm;
import jml2b.languages.ITranslatable;
import jml2b.languages.ITranslationResult;

public class PvsMethodCallForm extends MethodCallForm implements ITranslatable{

	

	public PvsMethodCallForm(MethodCallForm f) {
		super(f);
	}

	/**
	 * 
	 */
	private static final long serialVersionUID = 1L;

	public ITranslationResult toLang(int indent) throws LanguageException {
		PvsTranslationResult ptr =  new PvsTranslationResult(result);
		ptr.setLocalDecl(result + " : VAR " + resultType.toLang("PVS", 0).toUniqString() + "\n" + result + " : AXIOM " +
		                 m.toLang("PVS", 0).toUniqString() + "(" +
		                				(instance == null? "":(instance.toLang("PVS", 0).toUniqString() + ",")) +
		                				(param == null? "": (param.toLang("PVS", 0).toUniqString() + ",")) +
		                				result + ")");
		return ptr;
	}

}
