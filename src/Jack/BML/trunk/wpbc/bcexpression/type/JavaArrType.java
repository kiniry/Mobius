/*
 * Created on 19 mars 2004
 *
 * To change the template for this generated file go to
 * Window - Preferences - Java - Code Generation - Code and Comments
 */
package bcexpression.type;

import org.apache.bcel.generic.ArrayType;
import org.apache.bcel.generic.Type;

/**
 * @author io
 *
 * To change the template for this generated type comment go to
 * Window - Preferences - Java - Code Generation - Code and Comments
 */
public class JavaArrType extends JavaReferenceType { 
	private int size;
	private int dimensions;
	
	public JavaArrType(ArrayType _type) {
		super(_type);
		setSize(_type.getSize());
		setDimensions(_type.getDimensions());
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
}
