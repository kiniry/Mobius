/*
 * Created on Mar 4, 2004
 *
 * To change the template for this generated file go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
package constants;
import bcexpression.Expression;
import bcexpression.javatype.JavaType;
import bcexpression.substitution.RefFunction;
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
		JavaType _type) {
		super(_cpIndex, _CONSTANT_classref_index, _name);
		type = _type;
	}
	
	public Expression getType() {
		return type;
	}

}
