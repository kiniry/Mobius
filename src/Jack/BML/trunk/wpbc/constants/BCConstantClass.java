/*
 * Created on 8 mars 2004
 *
 * To change the template for this generated file go to
 * Window - Preferences - Java - Code Generation - Code and Comments
 */
package constants;

import org.apache.bcel.classfile.ConstantClass;

/**
 * @author io
 *
 * To change the template for this generated type comment go to
 * Window - Preferences - Java - Code Generation - Code and Comments
 */
public class BCConstantClass extends  BCConstant {
	private int nameIndex;
	
	public  BCConstantClass( ConstantClass _constantClass, int _cpIndex){
		super(_cpIndex);
		nameIndex  =_constantClass.getNameIndex();	
	}
	
	public int getNameIndex() {
		return  nameIndex;
	} 
}
