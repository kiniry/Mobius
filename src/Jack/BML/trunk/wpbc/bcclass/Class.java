/*
 * Created on Feb 23, 2004
 *
 * To change the template for this generated file go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
package bcclass;

import org.apache.bcel.generic.ConstantPoolGen;

/**
 * @author mpavlova
 *
 * To change the template for this generated type comment go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
public class Class {
	private Method[] methods;
	private ConstantPoolGen constantPoolGen;
	

	/**
	 * @return
	 */
	public ConstantPoolGen getConstantPoolGen() {
		return constantPoolGen;
	}

	/**
	 * @return
	 */
	public Method[] getMethods() {
		return methods;
	}

	/**
	 * @param gen
	 */
	public void setConstantPoolGen(ConstantPoolGen gen) {
		constantPoolGen = gen;
	}

	/**
	 * @param methods
	 */
	public void setMethods(Method[] methods) {
		this.methods = methods;
	}

}
