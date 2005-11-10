/*
 * Created on Mar 4, 2004
 *
 * To change the template for this generated file go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
package constants;


import org.apache.bcel.generic.ARRAYLENGTH;

import application.JavaApplication;
import bcclass.BCClass;
import bcclass.BCConstantPool;
import bcclass.BCField;
import bcexpression.Expression;
import bcexpression.ValueOfConstantAtState;
import bcexpression.javatype.JavaType;
import bcexpression.overload.RefFunction;
/**
 * @author mpavlova
 * 
 * class represents CONSTANT_fieldref_info structure
 * 
 * CONSTANT_Fieldref_info { 
 * 						   u1 tag; 
 * 						   u2 class_index; 
 * 						   u2 name_and_type_index; 
 * 						  }
 */
public class BCConstantFieldRef extends BCConstantRef implements RefFunction {
	/**
	 * the type of the field
	 */
	private JavaType type;

	public BCConstantFieldRef() {

	}

	/**
	 * @param _cpIndex -
	 *            the index into the constant pool under which this data
	 *            structure appears into the constant pool
	 * @param _CONSTANT_classref_index -
	 *            the index into the constant pool under which the class in
	 *            which the field is declared appears
	 * @param _name - the name under which the field appears in the source  code 
	 * @param _type -
	 *            the type of the field (the static one)
	 * 
	 */
	public BCConstantFieldRef(
		int _cpIndex,
		int _CONSTANT_classref_index,
		String _name,
		JavaType _type,
		BCConstantPool pool) {
		super(_cpIndex, _CONSTANT_classref_index, _name, pool);
		type = _type;
	
	}
	
	public BCField getBCField() {
		/*BCConstantPool cp = getConstantPool();*/
		BCConstantClass _constClass = getConstantClass();
		String _className = _constClass.getName();
		BCClass _class = JavaApplication.Application.getClass( _className);
		BCField[] fields = _class.getFields();
		if (fields == null) {
			return null;
		}
		for (int i = 0; i < fields.length; i++) {
			if (fields[i].getName().equals( getName()))	{
				return fields[i];
			}
		}
		return null;	
	}
	
	public Expression getType() {
		return type;
	}
	
	public Expression atState(int instrIndex) {
		ValueOfConstantAtState valueOfFieldAtState = new ValueOfConstantAtState(this , instrIndex);
		return valueOfFieldAtState;
	}
	/**
	 * two constant pool field references ( not obligatory from the same constant pool ) are equal
	 * if they are references to the same field, i.e. the class in which the field is declared is the
	 * same and the field names are the same
 	 */
	public boolean equals(Expression expr ) {
		
		// case for array lenght constants
		if ( ( expr instanceof ArrayLengthConstant ) && ( this instanceof ArrayLengthConstant)) {
			return true;
		}
		if ( ( expr instanceof ArrayLengthConstant ) && ( !(this instanceof ArrayLengthConstant)) ) {
			return false;
		}
		
		if ( ( this instanceof ArrayLengthConstant ) && ( !( expr  instanceof ArrayLengthConstant)) ) {
			return false;
		}
		
		
		// the case for MemUsed constants
		if ( ( expr instanceof MemUsedConstant ) && ( this instanceof MemUsedConstant)) {
			return true;
		}
		if ( ( expr instanceof MemUsedConstant ) && ( !(this instanceof MemUsedConstant)) ) {
			return false;
		}
		
		if ( ( this instanceof MemUsedConstant ) && ( !( expr  instanceof MemUsedConstant)) ) {
			return false;
		}
		
		
		if ( !(expr instanceof BCConstantFieldRef)) {
			return false;
		}
		BCConstantFieldRef constFieldRef = (BCConstantFieldRef )expr;
		String clazzWhereDeclared = constFieldRef.getConstantClass().getName();
		
		if (!(clazzWhereDeclared.equals( getConstantClass().getName()))) {
			return false;
		}
		String name = constFieldRef.getName();
		if (!(name.equals(getName()))) {
			return false;
		}
		JavaType type = (JavaType)constFieldRef.getType();
		if ( !(type.equals(getType() ) ) ) {
			return false;
		}
		return true;
	} 
	
}
