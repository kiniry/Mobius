/*
 * Created on 19 mars 2004
 *
 * To change the template for this generated file go to
 * Window - Preferences - Java - Code Generation - Code and Comments
 */
package bcexpression.javatype;

import org.apache.bcel.generic.ArrayType;
import org.apache.bcel.generic.Type;

import constants.BCConstantClass;

/**
 * @author io
 *
 * To change the template for this generated type comment go to
 * Window - Preferences - Java - Code Generation - Code and Comments
 */
public class JavaArrType extends JavaReferenceType { 
	private int size;
	private int dimensions;
	private JavaType elementType;
	private JavaType basicType;
	
	public JavaArrType(ArrayType _type, BCConstantClass _cc) {
		super(_type, _cc);
		setBasicType(_type.getBasicType());
		setElementType(_type.getElementType());
		setSize(_type.getSize());
		setDimensions(_type.getDimensions());
	}
	
	public JavaArrType(ArrayType _type)  {
		super(_type );
	}
	
	public JavaArrType(Class _class)  {
		this((ArrayType)Type.getType( _class) );
	}
	
	
	/**
	 * @return Returns the size.
	 */
	public int getSize() {
		return size;
	}
	/**
	 * @param size The size to set.
	 */
	private void setSize(int size) {
		this.size = size;
	}
	
	/**
	 * @return Returns the dimensions.
	 */
	public int getDimensions() {
		return dimensions;
	}
	
	/**
	 * @param dimensions The dimensions to set.
	 */
	private void setDimensions(int dimensions) {
		this.dimensions = dimensions;
	}
	
	/**
	 * @return
	 */
	public JavaType getElementType() {
		return elementType;
	}

	/**
	 * @param type
	 */
	private void setElementType( Type _type)  {
		elementType = JavaType.getJavaBasicType(_type) ;
	}
	
	private void setBasicType(Type _type) {
		basicType = JavaType.getJavaBasicType(_type);	
	}
	
	
	/**
	* @return basic type of array, i.e., for int[][][] the basic type is int
	*/
	public JavaType getBasicType() {
		return basicType;
	 }

}
