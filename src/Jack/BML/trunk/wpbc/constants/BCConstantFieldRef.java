/*
 * Created on Mar 4, 2004
 *
 * To change the template for this generated file go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
package constants;

import org.apache.bcel.classfile.ConstantClass;
import org.apache.bcel.classfile.ConstantFieldref;
import org.apache.bcel.generic.ConstantPoolGen;

import bcexpression.javatype.JavaType;

/**
 * @author mpavlova
 *
 * To change the template for this generated type comment go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
public class BCConstantFieldRef extends BCConstantRef  {
	
	private JavaType type;
	//private JavaType class_where_declared;
	
	public BCConstantFieldRef(ConstantFieldref ref , int _cpIndex) {
		super(ref.getClassIndex(), ref.getNameAndTypeIndex(), _cpIndex);
		
	}
	
	public BCConstantFieldRef(int _classIndex, int _nameAndTypeIndex , int _cpIndex, ConstantPoolGen _cpg) {
		super(_classIndex, _nameAndTypeIndex, _cpIndex );
		//class_where_declared = ((ConstantClass)_cpg.getConstant(_classIndex)).getBytes();
	}
	
	private void setType() {
		//acccess to the constant pool
	}
	
	public JavaType getType() {
		return type;
	}
}
