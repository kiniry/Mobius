/*
 * Created on 8 mars 2004
 *
 * To change the template for this generated file go to
 * Window - Preferences - Java - Code Generation - Code and Comments
 */
package constants;

import org.apache.bcel.classfile.ConstantInterfaceMethodref;

/**
 * @author io
 *
 * To change the template for this generated type comment go to
 * Window - Preferences - Java - Code Generation - Code and Comments
 */
public class BCConstantInterfaceMethodRef  extends BCConstantRef {

	public BCConstantInterfaceMethodRef (ConstantInterfaceMethodref ref, int _cpIndex ) {
		super(ref.getClassIndex(), ref.getNameAndTypeIndex(), _cpIndex);
	}
	
	public BCConstantInterfaceMethodRef (int _classIndex, int _nameAndTypeIndex , int _cpIndex) {
		super(_classIndex, _nameAndTypeIndex, _cpIndex );
	}
}
