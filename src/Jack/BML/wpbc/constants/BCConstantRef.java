/*
 * Created on 8 mars 2004
 *
 * To change the template for this generated file go to
 * Window - Preferences - Java - Code Generation - Code and Comments
 */
package constants;

import bcclass.BCConstantPool;


/**
 * @author mpavlova
 *
 * the class represents a constant pool constant : either 
 * CONSTANT_Fieldref_info, CONSTANT_MethodRef_info, CONSTANT_Class_info 
 */
public class BCConstantRef extends BCConstant {
	private int classIndex;
	
	private int CONSTANT_class_Index;
	
	private String name;

	private BCConstantPool cPool;
	public BCConstantRef( ) {
	}
	
	public BCConstantRef( int CONSTANT_X_info_index, int _CONSTANT_class_Index , String _name, BCConstantPool _cPool) {
		super(CONSTANT_X_info_index);
		CONSTANT_class_Index = _CONSTANT_class_Index;
		name = _name;
		cPool = _cPool;
	}
	
	public int getClassIndex() {
		return CONSTANT_class_Index;
	}	
	
	public String getName() {
		return name;
	}
	
	public BCConstantClass getConstantClass() {
		return (BCConstantClass)cPool.getConstant(getClassIndex());
	}
	
	public String getAbsoluteName() {
		String className = getConstantClass().getName();
		String absoluteName = className + "." + name;
		return absoluteName;
	}
	
	public String toString() {
		return getAbsoluteName();
	}
	/**
	 * @return Returns the cPool.
	 *//*
	protected BCConstantPool getConstantPool() {
		return cPool;
	}*/
}
