/*
 * Created on 8 mars 2004
 *
 * To change the template for this generated file go to
 * Window - Preferences - Java - Code Generation - Code and Comments
 */
package bytecode_wp.constants;

import jml2b.IJml2bConfiguration;
import bytecode_to_JPO.B2JPackage;
import bytecode_wp.bc.io.ReadAttributeException;
import bytecode_wp.bcclass.BCClass;
import bytecode_wp.bcclass.BCConstantPool;
import bytecode_wp.bcclass.BCField;
import bytecode_wp.bcexpression.javatype.JavaReferenceType;
import bytecode_wp.bytecode.block.IllegalLoopException;


/**
 * @author mpavlova
 *
 * the class represents a constant pool constant : either 
 * CONSTANT_Fieldref_info, CONSTANT_MethodRef_info, CONSTANT_Class_info 
 */
public class BCConstantRef extends BCConstant {
	//private int classIndex;
	
	private int CONSTANT_class_Index;
	
	private String name;

	private boolean initIsStatic = false; 
	private boolean isStatic;
	
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
	
	
	public JavaReferenceType getClassWhereDeclared() {
		BCConstantClass classConstant = getConstantClass();
//		assert (classConstant != null);
		if ( classConstant == null ) {
			return null;
		}
		JavaReferenceType classTypeWhereDeclared = JavaReferenceType.getJavaRefType(classConstant.getName());
		return classTypeWhereDeclared;
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
	public boolean isStatic() {
		if (initIsStatic) {
			return isStatic;
		}
		initIsStatic = true;
		String clName = getConstantClass().getName() ;
		IJml2bConfiguration config = cPool.getConfig();
		BCClass c = ((B2JPackage) config.getPackage()).getClass( clName );
		BCField f = null;
		try {
			f = c.lookupField(config, name);
		} catch (ReadAttributeException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		} catch (IllegalLoopException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		if (f != null) {
			isStatic = f.isStatic();
		}
		return isStatic;
	}
}
