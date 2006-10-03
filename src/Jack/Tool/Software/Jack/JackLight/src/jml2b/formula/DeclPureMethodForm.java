/*
 * Created on Sep 14, 2005
 *
 * To change the template for this generated file go to
 * Window&gt;Preferences&gt;Java&gt;Code Generation&gt;Code and Comments
 */
package jml2b.formula;

import java.util.Set;
import java.util.Vector;

public class DeclPureMethodForm extends Formula {

	/**
	 * 
	 */
	private static final long serialVersionUID = 1L;
	protected Formula method;
	protected Formula instanceType;
	protected QuantifiedVarForm params;
	protected String result;
	protected TTypeForm resultType;
	protected Formula ensures;

	public DeclPureMethodForm(Formula form, Formula form2, QuantifiedVarForm w, String ww, TTypeForm rt,Formula f) {
		super(DECL_PURE_METHOD);
		method = form;
		instanceType = form2;
		params = w;
		result = ww;
		resultType = rt;
		ensures = f;
	}

	public DeclPureMethodForm(DeclPureMethodForm f) {
		super(f.getNodeType());
		this.method = f.method;
		this.instanceType = f.instanceType;
		this.params = f.params;
		this.result = f.result;
		this.resultType = f.resultType;
		this.ensures = f.ensures;
	}
	
	public BasicType getBasicType() {
		return BasicType.PropType;
	}

	public Object clone() {
		return new DeclPureMethodForm((Formula) method.clone(),
		                              instanceType == null ? null : (Formula) instanceType
				.clone(), 
				params == null ? null : (QuantifiedVarForm) params.clone(), result, resultType, (Formula) ensures.clone());
	}

	public void processIdent() {
		method.processIdent();
		if (instanceType != null)
			instanceType.processIdent();
		if (params != null)
		params.processIdent();
		ensures.processIdent();
	}

	public Formula instancie(Formula b) {
		method.instancie(b);
		if (instanceType != null)
			instanceType.instancie(b);
		ensures.instancie(b);
		return this;
	}

	public void getFields(Set fields) {
		method.getFields(fields);
		if (instanceType != null)
			instanceType.getFields(fields);
		ensures.getFields(fields);
	}

	public Formula sub(Formula a, Formula b, boolean subInCalledOld) {
		Formula tmpmethod = null, tmpinstancetype = null, tmpensures = null;
		if (!(a.getNodeType() == Ja_IDENT && params != null && params.contain(a))) {
		tmpmethod = method.sub(a, b, subInCalledOld);
		if (instanceType != null)
			tmpinstancetype = instanceType.sub(a, b, subInCalledOld);
		tmpensures = ensures.sub(a, b, subInCalledOld);
		if (tmpmethod == method && tmpinstancetype == instanceType && tmpensures == ensures)
			return this;
		else
			return new DeclPureMethodForm(tmpmethod, tmpinstancetype, params, result, resultType, tmpensures);
		} else
			return this;
	}

	public Formula suppressSpecialOld(int token) {
		Formula tmpmethod = null, tmpinstancetype = null, tmpensures = null;
		tmpmethod = method.suppressSpecialOld(token);
		if (instanceType != null)
			tmpinstancetype = instanceType.suppressSpecialOld(token);
		tmpensures = ensures.suppressSpecialOld(token);
		if (tmpmethod == method && tmpinstancetype == instanceType && tmpensures == ensures)
			return this;
		else
			return new DeclPureMethodForm(tmpmethod, tmpinstancetype, params, result, resultType, tmpensures);
	}

	public Formula subIdent(String a, Formula b) {
		Formula tmpmethod = null, tmpinstancetype = null, tmpensures = null;
		if (!(params != null && params.contain(a))) {
		tmpmethod = method.subIdent(a, b);
		if (instanceType != null)
			tmpinstancetype = instanceType.subIdent(a, b);
		if(ensures != null)
			tmpensures = ensures.subIdent(a, b);
		if (tmpmethod == method && tmpinstancetype == instanceType && tmpensures == ensures)
			return this;
		else
			return new DeclPureMethodForm(tmpmethod, tmpinstancetype, params, result, resultType, tmpensures);	
		} else
				return this;
	}

	public boolean equals(Object f) {
		if (f instanceof DeclPureMethodForm) {
			DeclPureMethodForm new_f = (DeclPureMethodForm) f;
			return method.equals(new_f.method)
					&& (instanceType == null ? new_f.instanceType == null : instanceType.equals(new_f.instanceType))
					&& ensures.equals(new_f.ensures) && result.equals(new_f.result) && resultType.equals(new_f.resultType)
					&& (params == null ? new_f.params == null : params.equals(new_f.params));
		} else
			return false;
	}

	public boolean isObvious(boolean atTheEnd) {
		return false;
	}

	public void garbageIdent() {
		method.garbageIdent();
		if (instanceType != null)
			instanceType.garbageIdent();
		if (params != null)
		params.garbageIdent();
		ensures.garbageIdent();
	}

	public int contains(Vector selectedFields) {
		return ensures.contains(selectedFields);
	}

}
