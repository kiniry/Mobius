package annot.constants;

import annot.bcclass.BCConstantPool;
import annot.bcexpression.javatype.JavaType;

/**
 * @author mpavlova
 *     
 *     CONSTANT_InterfaceMethodref_info {
 *   	   u1 tag;
 *   	   u2 class_index;
 *   	   u2 name_and_type_index;
 *      }
 */
public class BCConstantInterfaceMethodRef  extends BCConstantMethodRef {
	
	public BCConstantInterfaceMethodRef (  int _cpIndex, int _CONSTANT_class_info_index, String _name, JavaType _returnType,  JavaType[] _argTypes, BCConstantPool pool) {
		super( _cpIndex, _CONSTANT_class_info_index, _name, _returnType, _argTypes,pool );
	}
}
