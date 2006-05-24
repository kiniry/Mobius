/*
 * Created on May 4, 2005
 *
 * To change the template for this generated file go to
 * Window&gt;Preferences&gt;Java&gt;Code Generation&gt;Code and Comments
 */
package jml2b.structure.bytecode;

import java.util.Vector;

import jml2b.IJml2bConfiguration;
import jml2b.exceptions.Jml2bException;
import jml2b.link.LinkContext;
import jml2b.structure.IAParameters;
import jml2b.structure.java.Type;
import jml2b.structure.jml.SpecCase;


/**
 *
 *  @author L. Burdy
 **/
public class ClassDefaultConstructor extends ClassMethod {

	static final long serialVersionUID = 1823472530129815672L;

	public ClassDefaultConstructor(ClassFile cf) {
	super(cf);
	}

	public boolean isExternalVisible() {
		return false;
}
public boolean isFinal() {
		return false;
}
public boolean isPackageVisible() {
	return false;
}
public boolean isPrivate() {
	return true;
}
public boolean isProtected() {
	return true;
}
public boolean isProtectedNotSpecPublic() {
	return true;
}
public boolean isStatic() {
	return false;
}

public void parse(IJml2bConfiguration config) throws Jml2bException {
	returnType = null;
	LinkContext lc = new LinkContext(definingClass);
	lc.currentMethod = this;
	sc = new Vector();
	sc.add(new SpecCase(config, lc));
}

/**
 * @param param_types
 * @param argumentTypes
 * @return
 */
public boolean exactMatch(Vector param_types) {
	return (param_types.size() == 0) ;
}

public boolean matchingSignaturesF(Vector field_types) {
	return field_types.size() == 0;
}

public boolean isCompatible(Vector param_types) {
	return param_types.size()==0;
}


public String getName() {
	return definingClass.getName();
}

public String getSignature() {
	return "";
}

/* (non-Javadoc)
 * @see jml2b.structure.AMethod#getSign()
 */
public IAParameters getParams() {
	return new ClassParameters();
}

public boolean isConstructor() {
	return true;
}

public Type getReturnType() {
	return null;
}

public boolean isDefaultConstructor(String name) {
	return true;
}
	
}
