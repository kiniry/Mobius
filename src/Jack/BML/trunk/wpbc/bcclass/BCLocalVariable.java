/*
 * Created on Mar 4, 2004
 *
 * To change the template for this generated file go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
package bcclass;

import org.apache.bcel.generic.LocalVariableGen;


import bcexpression.javatype.JavaType;

/**
 * @author mpavlova
 *
 * To change the template for this generated type comment go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
public class BCLocalVariable {
	private  int index;
	private  int length;
	private String name;
	private JavaType type; 
	private  int start_pc;
	
//	private  int  name_index;	
	
	public BCLocalVariable(String _name, int _start_pc,  int _index,  JavaType _type ) {
		name = _name;
		start_pc = _start_pc;
		index = _index;
		type = _type;
//		length =  _length;
//		name_index = _name_index;
//		signature_index = _signature_index;
		
	}

	public BCLocalVariable(LocalVariableGen lv) {
		this(lv.getName(), lv.getStart().getPosition() ,  lv.getIndex(), JavaType.getJavaType( lv.getType()));	
	}

	/**
	 * @return
	 */
	public int getIndex() {
		return index;
	}

	/**
	 * @return
	 */
	public int getLength() {
		return length;
	}

	/**
	 * @return
	 */
	public int getStart_pc() {
		return start_pc;
	}

//	/**
//	 * @return
//	 */
//	public int getName_index() {
//		return name_index;
//	}
//
//	/**
//	 * @return
//	 */
//	public int getSignature_index() {
//		return signature_index;
//	}
//
	

	/**
	 * @return
	 */
	public JavaType getType() {
		return type;
	}

}
