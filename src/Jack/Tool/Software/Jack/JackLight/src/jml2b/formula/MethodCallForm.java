/*
 * Created on Sep 14, 2005
 *
 * To change the template for this generated file go to
 * Window&gt;Preferences&gt;Java&gt;Code Generation&gt;Code and Comments
 */
package jml2b.formula;

import java.util.Set;
import java.util.Vector;

public class MethodCallForm extends Formula {

	/**
	 * 
	 */
	private static final long serialVersionUID = 1L;

	protected Formula m;

	protected Formula param;

	protected Formula instance;

	protected final String result;
	
	protected final Formula resultType;

	public MethodCallForm(String m, Formula p, Formula i, String ww, Formula rt) {
		super(IFormToken.METHOD_CALL);
		this.m = new TerminalForm(m);
		param = p;
		instance = i;
		result = ww;
		resultType = rt;
	}

	private MethodCallForm(Formula m, Formula p, Formula i, String ww, Formula rt) {
		super(IFormToken.METHOD_CALL);
		this.m = m;
		param = p;
		instance = i;
		result = ww;
		resultType = rt;
	}

	public MethodCallForm(MethodCallForm f) {
		super(f.getNodeType());
		this.m = f.m;
		this.param = f.param;
		this.instance = f.instance;
		this.result = f.result;
		this.resultType = f.resultType;
	}

	public BasicType getBasicType() {
		return BasicType.PropType;
	}

	public Object clone() {
		return new MethodCallForm(m, param, instance, result,resultType);
	}

	public void processIdent() {
		m.processIdent();
		if (param != null)
			param.processIdent();
		if (instance != null)
			instance.processIdent();
	}

	public Formula instancie(Formula b) {
		m = m.instancie(b);
		if (param != null)
			param = param.instancie(b);
		if (instance != null)
			instance = instance.instancie(b);
		return this;
	}

	public void getFields(Set fields) {
		m.getFields(fields);
		if (param != null)
			param.getFields(fields);
		if (instance != null)
			instance.getFields(fields);
	}

	public Formula sub(Formula a, Formula b, boolean subInCalledOld) {
		Formula tmpparam = null, tmpinstance = null;
		if (param != null)
			tmpparam = param.sub(a, b, subInCalledOld);
		if (instance != null)
			tmpinstance = instance.sub(a, b, subInCalledOld);
		if (tmpparam == param && tmpinstance == instance)
			return this;
		else
			return new MethodCallForm(m, tmpparam, tmpinstance, result,resultType);
	}

	public Formula suppressSpecialOld(int token) {
		Formula tmpparam = null, tmpinstance = null;
		if (param != null)
			tmpparam = param.suppressSpecialOld(token);
		if (instance != null)
			tmpinstance = instance.suppressSpecialOld(token);
		if (tmpparam == param && tmpinstance == instance)
			return this;
		else
			return new MethodCallForm(m, tmpparam, tmpinstance, result, resultType);
	}

	public Formula subIdent(String a, Formula b) {
		Formula tmpparam = null, tmpinstance = null;
		if (param != null)
			tmpparam = param.subIdent(a, b);
		if (instance != null)
			tmpinstance = instance.subIdent(a, b);
		if (tmpparam == param && tmpinstance == instance)
			return this;
		else
			return new MethodCallForm(m, tmpparam, tmpinstance, result, resultType);
	}

	public boolean equals(Object f) {
		if (f instanceof MethodCallForm) {
			MethodCallForm new_f = (MethodCallForm) f;
			return m.equals(new_f.m)
					&& (param == null ? new_f.param == null : param
							.equals(new_f.param))
					&& (instance == null ? new_f.instance == null : instance
							.equals(new_f.instance))
					&& result.equals(new_f.result)
					&& resultType.equals(new_f.resultType);
		} else
			return false;
	}

		public boolean isObvious(boolean atTheEnd) {
		return false;
	}

	public void garbageIdent() {
		if (param != null)
			param.garbageIdent();
		if (instance != null)
			instance.garbageIdent();

	}

	public int contains(Vector selectedFields) {
		return (param == null ? 0 : param.contains(selectedFields))
				+ (instance == null ? 0 : instance.contains(selectedFields));
	}

}
