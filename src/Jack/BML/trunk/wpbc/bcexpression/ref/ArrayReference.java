/*
 * Created on Apr 22, 2004
 *
 * To change the template for this generated file go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
package bcexpression.ref;

import bcexpression.Expression;
import bcexpression.NumberLiteral;
import bcexpression.javatype.JavaArrType;
import bcexpression.javatype.JavaType;

/**
 * @author mpavlova
 *
 * this class is representing an array reference 
 */
public class ArrayReference extends Reference  {
	/**
	 * length of the array
	 */
	private Expression length;

	/**
	 *  number of dimensions of the array
	 */
	private Expression dimensions;

	/**
	 * array of the objects that are in the array
	 */
	private Expression element;
	
	private JavaArrType type;
	
	/**
	 * @param _id - an unique identificator for this object 
	 * @param _type - type of the elements 
	 * @param  _elements - the elements of the array
	 */
	public ArrayReference(int _id, JavaType _elType, Expression _length, Expression _element ) {
		super(_id, _elType);
		length = _length;	
		element = _element;
	}
	
	/**
	 * constructor used for one dimensional arrays
	 * @param _id - an unique identificator for this object 
	 * @param _type - type of the elements 
	 * @param  _elements - the elements of the array
	 */
	public ArrayReference(int _id, JavaType _elType, Expression _length ) {
		super(_id, _elType);
		length = _length;	
	}



	public Expression getDimensions() {
		return new NumberLiteral( type.getDimensions());
	}

	/**
	 * @return the array length if it is one dimensional 
	 */
	public Expression getLength() {
		return length; 
	}
}
