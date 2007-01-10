/*
 * Created on 19 mars 2004
 *
 */
package bytecode_wp.bcexpression.javatype;

import org.apache.bcel.generic.ArrayType;
import org.apache.bcel.generic.Type;

/**
 * @author io
 * 
 * To change the template for this generated type comment go to Window -
 * Preferences - Java - Code Generation - Code and Comments
 */
public class JavaArrType extends JavaReferenceType {
	private int size;

	private int dimensions;

	private JavaType elementType;

	private JavaType basicType;

	public static final JavaArrType ARRTYPE = new JavaArrType();

	private JavaArrType() {

	}

	protected JavaArrType(JavaType _type) {
		if (_type instanceof JavaArrType) {
			setElementType(((JavaArrType) _type).getElementType());
			setBasicType(((JavaArrType) _type).getBasicType());
			setDimensions(((JavaArrType) _type).getDimensions() + 1);
			return;
		}
		setElementType(_type);
		setBasicType(_type);
		setDimensions(1);
	}

	protected JavaArrType(ArrayType _type) {
		super(_type);
		setBasicType(JavaType.getJavaType(_type.getBasicType()));
		setElementType(JavaType.getJavaType(_type.getElementType()));
		setSize(_type.getSize());
		setDimensions(_type.getDimensions());
	}

	protected JavaArrType(Class _class) {
		this((ArrayType) Type.getType(_class));
	}

	/**
	 * @return Returns the size.
	 */
	public int getSize() {
		return size;
	}

	/**
	 * @param size
	 *            The size to set.
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
	 * @param dimensions
	 *            The dimensions to set.
	 */
	private void setDimensions(int dimensions) {
		this.dimensions = dimensions;
	}

	/**
	 * @return
	 */
	public JavaType getElementType() {
		if (elementType == null) {
			return JavaReferenceType.ReferenceType;
		}
		return elementType;
	}

	/**
	 * First looks for the corresp?nding object representing the type if it is
	 * already charged as a JavaType object. If it is already created it returns
	 * the object, otherwise it is cretaed by the JavaType object and is
	 * returned example : for int[][] sets to int[] the field elementType
	 * 
	 * @param type
	 */
	private void setElementType(JavaType _type) {
		elementType = _type;
	}

	/**
	 * example : for int[][] sets to int the field basicType
	 * 
	 * @param _type
	 */
	private void setBasicType(JavaType _type) {
		basicType = _type;
	}

	/**
	 * @return basic type of array, i.e., for int[][][] the basic type is int
	 */
	public JavaType getBasicType() {
		return basicType;
	}

	public static boolean subType(JavaArrType _type1, JavaArrType _type2) {
		String signatureType2 = (_type2.getBcelType()).getSignature();
		if (signatureType2.equals("Ljava/lang/Object;")) {
			return true;
		}
		JavaType elType1 = _type1.getElementType();
		JavaType elType2 = _type2.getElementType();
		if ((elType1 instanceof JavaBasicType)
				&& (elType2 instanceof JavaBasicType) && (elType1 == elType2)) {
			return true;
		}
		if ((elType1 instanceof JavaBasicType)
				&& (elType2 instanceof JavaBasicType) && (elType1 != elType2)) {
			return false;
		}
		if (!(elType1 instanceof JavaBasicType)
				&& (elType2 instanceof JavaBasicType)) {
			return false;
		}
		if ((elType1 instanceof JavaBasicType)
				&& !(elType2 instanceof JavaBasicType)) {
			return false;
		}

		return JavaReferenceType.subType((JavaReferenceType) elType1,
				(JavaReferenceType) elType2);

		/*
		 * if (! JavaType.subType(_type1.getBasicType(), _type2.getBasicType())) {
		 * return false; } if (! JavaType.subType(_type1.getElementType(),
		 * _type1.getElementType())) { return false; } if
		 * (_type1.getDimensions() != _type2.getDimensions()) { return false; }
		 * if (_type1.getSize() != _type2.getSize()) { return false; }
		 */

	}

	public String getSignature() {
		String signature = super.getSignature();
		if (signature.endsWith(";")) {
			signature = signature.substring(0, signature.length() - 1);
		}
		return signature;

	}
}
