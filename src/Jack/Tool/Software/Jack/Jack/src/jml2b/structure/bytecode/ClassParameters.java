/*
 * Created on May 4, 2005
 *
 * To change the template for this generated file go to
 * Window&gt;Preferences&gt;Java&gt;Code Generation&gt;Code and Comments
 */
package jml2b.structure.bytecode;

import java.io.Serializable;
import java.util.Vector;

import jml2b.IJml2bConfiguration;
import jml2b.pog.util.IdentifierResolver;
import jml2b.structure.IAParameters;
import jml2b.structure.java.Field;
import jml2b.structure.java.ParsedItem;
import jml2b.structure.java.Type;
import jml2b.structure.statement.Statement;

import org.apache.bcel.classfile.Method;

/**
 *
 *  @author L. Burdy
 **/
public class ClassParameters extends  IAParameters implements Serializable{

	static final long serialVersionUID = 5004872031444756772L;

	Type[] params;
	Vector fields = new Vector();
	/**
	 * @param m
	 */
	public ClassParameters(IJml2bConfiguration config, Method m) throws jml2b.exceptions.Jml2bException {
		params = new Type[m.getArgumentTypes().length];
		for (int i=0;i < params.length;i++)
			params[i] = ClassField.getType(config, m.getArgumentTypes()[i]);
	}
	
	/**
	 * 
	 */
	public ClassParameters() {
		params= new Type[0];
	}

	public Type getType(int i) {
		return params[i];
	}
	
	public /*@ pure @*/ Vector getSignature() {
		if(fields.size() != params.length) {// lazy style
			fields = new Vector();
			for (int i= 0; i < params.length; i++) {
				Field fi = new Field(ParsedItem.$empty, params[i], Statement.fresh());
				fields.add(fi);
				fi.nameIndex = IdentifierResolver.addIdent(fi);
			}
		} 
		return fields;
	}
	
	public int nparams() {
		return params.length;
	}
	
	public String toString(char c) {
			return "";
	}
}
