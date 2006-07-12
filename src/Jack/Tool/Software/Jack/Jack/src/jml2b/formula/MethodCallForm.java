/*
 * Created on Sep 14, 2005
 *
 * To change the template for this generated file go to
 * Window&gt;Preferences&gt;Java&gt;Code Generation&gt;Code and Comments
 */
package jml2b.formula;

import java.io.IOException;
import java.util.Set;
import java.util.Vector;

import jml2b.IJml2bConfiguration;
import jml2b.exceptions.LoadException;
import jml2b.structure.java.IJmlFile;
import jml2b.util.IOutputStream;
import jml2b.util.JpoInputStream;

public class MethodCallForm extends Formula {

	/**
	 * 
	 */
	private static final long serialVersionUID = 1L;

	/** method name */
	protected Formula m;

	/** method parameter */
	protected Formula param;

	/** instance ? */
	protected Formula instance;

	/** a name for the result */
	protected final String result;
	
	/** the result type */
	protected final Formula resultType;

	public MethodCallForm(String m, Formula param, Formula instance, String resultName, Formula resultType) {
		super(IFormToken.METHOD_CALL);
		this.m = new TerminalForm(m);
		this.param = param;
		this.instance = instance;
		result = resultName;
		this.resultType = resultType;
	}

	private MethodCallForm(Formula m, Formula p, Formula i, String ww, Formula rt) {
		super(IFormToken.METHOD_CALL);
		this.m = m;
		this.param = p;
		this.instance = i;
		this.result = ww;
		this.resultType = rt;
	}

	public MethodCallForm(IJml2bConfiguration config, IJmlFile fi,
			JpoInputStream s) throws IOException, LoadException {
		super(IFormToken.METHOD_CALL);
		m = Formula.create(config, s, fi);
		boolean b = s.readBoolean();
		if (b)
			param = Formula.create(config, s, fi);
		b = s.readBoolean();
		if (b)
			instance = Formula.create(config, s, fi);
		result = s.readUTF();
		resultType = Formula.create(config, s, fi);
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

	public boolean is(Formula f) {
		if (f instanceof MethodCallForm) {
			MethodCallForm new_f = (MethodCallForm) f;
			return m.is(new_f.m)
					&& ((param == null) ? (new_f.param == null) : param
							.is(new_f.param))
					&& ((instance == null) ? (new_f.instance == null)
							: instance.is(new_f.instance))
					&& result.equals(new_f.result)
					&& resultType.equals(new_f.resultType);
		} else
			return false;
	}

	public boolean isObvious(boolean atTheEnd) {
		return false;
	}

	public void save(IJml2bConfiguration config, IOutputStream s, IJmlFile jf)
			throws IOException {
		s.writeByte(getNodeType());
		m.save(config, s, jf);
		if (param == null)
			s.writeBoolean(false);
		else {
			s.writeBoolean(true);
			param.save(config, s, jf);
		}
		if (instance == null)
			s.writeBoolean(false);
		else {
			s.writeBoolean(true);
			instance.save(config, s, jf);
		}
		s.writeUTF(result);
		resultType.save(config, s, jf);
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
