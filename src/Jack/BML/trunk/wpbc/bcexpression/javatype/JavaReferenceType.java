/*
 * Created on Mar 23, 2004
 *
 * To change the template for this generated file go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
package bcexpression.javatype;

import org.apache.bcel.generic.ReferenceType;
import org.apache.bcel.generic.Type;

import constants.BCConstantClass;


/**
 * @author mpavlova
 *
 * To change the template for this generated type comment go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
public class JavaReferenceType extends JavaType {
	private BCConstantClass bcc;
		
	/**
	 * @param _type
	 */
	protected JavaReferenceType(ReferenceType _type, BCConstantClass _cc) {
		super(_type, _cc, JavaType.COMPUTATIONAL_TYPE_1);
	}
	
	/**
	 * @param _type
	 */
	protected JavaReferenceType(Class _class, BCConstantClass _cc) {
		this((ReferenceType)Type.getType(_class), _cc);
	}
	
	
	///////////////////////////////////////////////
	/////
	////////////////////////////////////////
	/**
	 * @param _type
	 * constructor used for default types, that do not have data structure representing them in the constant pool
	 * that is do not have a corresponding ConstantClass object
	 */
	protected JavaReferenceType(ReferenceType _type ) {
		super(_type, JavaType.COMPUTATIONAL_TYPE_1);
	}

	/**
	 * @param _type
	 * constructor used for default types, that do not have data structure representing them in the constant pool
	 * that is do not have a corresponding ConstantClass object
	 */
	protected JavaReferenceType(Class _class) {
		this((ReferenceType)Type.getType(_class));

	}
	
	/**
	 * 
	 * @param _bcc
	 * sets the constantClass_info from the constant pool that describe this class  
	 */
	public void setBCConstantClass(BCConstantClass _bcc) {
		bcc = _bcc;
	}
	
	/**
	 * @param _bcc
	 * sets the constantClass_info from the constant pool that describe this class  
	 */
	public BCConstantClass getBCConstantClass() {
		return bcc ;
	}

}
