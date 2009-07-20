/*
 * Created on Mar 4, 2004
 *
 * To change the template for this generated file go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
package bytecode_wp.constants;

import bytecode_wp.bcclass.BCConstantPool;
import bytecode_wp.bcclass.utils.MethodSignature;
import bytecode_wp.bcexpression.javatype.JavaType;
import bytecode_wp.bcexpression.overload.RefFunction;

/**
 * @author mpavlova
 * rerpesents a constant pool data structure
 * 
 *     CONSTANT_Methodref_info {
 *   	   u1 tag;
 *   	   u2 class_index;
 *   	   u2 name_and_type_index;
 *     }
 *
 */
public class BCConstantMethodRef  extends BCConstantRef implements RefFunction {
	JavaType returnType ;
	JavaType[] argTypes;
	
	public BCConstantMethodRef (  int _cpIndex, int _CONSTANT_classref_info_index, String _name , JavaType _returnType,  JavaType[] _argTypes, BCConstantPool pool) {
		super( _cpIndex, _CONSTANT_classref_info_index, _name, pool);
		returnType = _returnType;
		argTypes = _argTypes;
	}
	
	/**
	 * @return
	 */
	public JavaType getReturnType() {
		return returnType;
	}

	/**
	 * @return
	 */
	public JavaType[] getArgTypes() {
		return argTypes;
	}
	
	public String getSignature() {

		String signature =MethodSignature.getSignature(getArgTypes(), getReturnType() );
		return signature;
		/*StringBuffer buf = new StringBuffer("(");
		int length = (argTypes == null)? 0 : argTypes.length;
		
		for(int i=0; i < length; i++)
		buf.append(argTypes[i].getSignature());
		buf.append(')');
		buf.append(returnType.getSignature());
		return buf.toString();*/
		
		/*String args = "(";
		if ( (argTypes == null ) || (argTypes.length == 0)  ) {
			args = args + ")";
		} else {
			for (int i = 0;  i < argTypes.length; i++) {
				args = args + argTypes[i].getSignature(); 
			}
			args = args + ")";
		}
		String signature = args + returnType.toString();
//		Util.dump(signature);
		return signature; */
	}
}
