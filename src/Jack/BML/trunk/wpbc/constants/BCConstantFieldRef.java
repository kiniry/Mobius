/*
 * Created on Mar 4, 2004
 *
 * To change the template for this generated file go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
package constants;

import org.apache.bcel.classfile.ConstantFieldref;

/**
 * @author mpavlova
 *
 * To change the template for this generated type comment go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
public class BCConstantFieldRef extends BCConstantRef  {
	
	
	public BCConstantFieldRef(ConstantFieldref ref , int _cpIndex) {
		super(ref.getClassIndex(), ref.getNameAndTypeIndex(), _cpIndex);
		
	}
	
	public BCConstantFieldRef(int _classIndex, int _nameAndTypeIndex , int _cpIndex) {
		super(_classIndex, _nameAndTypeIndex, _cpIndex );
	}
	


}
