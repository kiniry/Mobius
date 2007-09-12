package annot.bcclass;

import org.apache.bcel.classfile.Field;

import annot.bcexpression.javatype.JavaBasicType;
import annot.bcexpression.javatype.JavaType;

public class BCField extends AccessFlags {
	private String name;
	private JavaType type;
	
	public BCField(Field f) {
		super(f.getAccessFlags() );
		name = f.getName();
		type = JavaType.getJavaType(f.getType());	 
	}
		
//	public String getName( ) {
//		return name;
//	}
//	
//	public JavaType getType() {
//		if ( type == JavaBasicType.JavaBOOLEAN) {
//			return JavaBasicType.JavaINT;
//		}
//		return type;
//	}
//
//	/**
//	 * @return
//	 */
//	public boolean isVisible() {
//		
//		return isPublic() || isProtected();
//	}
//	
//	public String toString() {
//	
//		return name;
//	}
}
