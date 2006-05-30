package pvsPlugin;

import jml2b.exceptions.LanguageException;
import jml2b.formula.DeclPureMethodForm;
import jml2b.formula.TTypeForm;
import jml2b.languages.ITranslatable;
import jml2b.languages.ITranslationResult;

public class PvsDeclPureMethodForm extends DeclPureMethodForm implements ITranslatable {

	/**
	 * 
	 */
	private static final long serialVersionUID = 1L;

	public PvsDeclPureMethodForm(DeclPureMethodForm form) {
		super(form);
	}
	
	public ITranslationResult toLang(int indent) throws LanguageException {
		TTypeForm ct = (TTypeForm)this.instanceType;
		PvsTranslationResult ptr =  new PvsTranslationResult("true");
		ptr.addPredDecl(method.toLang("PVS", 0).toUniqString() +
		                				(ct == null ? "" : "(this: REFERENCES)") +
		                				(params == null ? "" : new PvsTranslationResult(params).toUniqString()) +
		                				(result == null ? "" : "("+ result + " : " + resultType.toLang("PVS", 0).toUniqString()) +") : bool = "	+ 
		                				this.ensures.toLang("PVS", 0).toUniqString());
		                				return ptr;}

}
