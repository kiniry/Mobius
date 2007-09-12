package annot.constants;

import annot.bcclass.BCConstantPool;

//import jml2b.IJml2bConfiguration;
//import bytecode_to_JPO.B2JPackage;
//import annot.bcio.ReadAttributeException;
//import annot.bcclass.BCClass;
//import annot.bcclass.BCConstantPool;
//import annot.bcclass.BCField;
//import bytecode_wp.bcexpression.javatype.JavaReferenceType;
//import bytecode_wp.bytecode.block.IllegalLoopException;

public class BCConstantRef extends BCConstant {
//	//private int classIndex;
	private int CONSTANT_class_Index;
	protected String name;
//	private boolean initIsStatic = false; 
//	private boolean isStatic;
	private BCConstantPool cPool;
	
	public BCConstantRef( ) {
	}
	
	public BCConstantRef( int CONSTANT_X_info_index, int _CONSTANT_class_Index , String _name, BCConstantPool _cPool) {
		super(CONSTANT_X_info_index);
		CONSTANT_class_Index = _CONSTANT_class_Index;
		name = _name;
		cPool = _cPool;
	}
	
//	public int getClassIndex() {
//		return CONSTANT_class_Index;
//	}	
//	
//	public String getName() {
//		return name;
//	}
//	
//	public BCConstantClass getConstantClass() {
//		return (BCConstantClass)cPool.getConstant(getClassIndex());
//	}
//	
//	
//	public JavaReferenceType getClassWhereDeclared() {
//		BCConstantClass classConstant = getConstantClass();
////		assert (classConstant != null);
//		if ( classConstant == null ) {
//			return null;
//		}
//		JavaReferenceType classTypeWhereDeclared = JavaReferenceType.getJavaRefType(classConstant.getName());
//		return classTypeWhereDeclared;
//	}
//	
//	public String getAbsoluteName() {
//		String className = getConstantClass().getName();
//		String absoluteName = className + "." + name;
//		return absoluteName;
//	}
//	
//	public String toString() {
//		return getAbsoluteName();
//	}
//	/**
//	 * @return Returns the cPool.
//	 *//*
//	protected BCConstantPool getConstantPool() {
//		return cPool;
//	}*/
//	public boolean isStatic() {
//		if (initIsStatic) {
//			return isStatic;
//		}
//		initIsStatic = true;
//		String clName = getConstantClass().getName() ;
//		IJml2bConfiguration config = cPool.getConfig();
//		BCClass c = ((B2JPackage) config.getPackage()).getClass( clName );
//		BCField f = null;
//		try {
//			f = c.lookupField(config, name);
//		} catch (ReadAttributeException e) {
//			// TODO Auto-generated catch block
//			e.printStackTrace();
//		} catch (IllegalLoopException e) {
//			// TODO Auto-generated catch block
//			e.printStackTrace();
//		}
//		if (f != null) {
//			isStatic = f.isStatic();
//		}
//		return isStatic;
//	}
}
