package annot.bcexpression;

import org.apache.bcel.generic.ArrayType;
import org.apache.bcel.generic.Type;

import annot.textio.BMLConfig;

/**
 * This class represents an array type.
 * Use {@link #getSingleType()} to get single element's type.
 * 
 * @author tomekb
 */
public class JavaArrayType extends JavaType1 {

	/**
	 * Type's (BCEL) signature, eg. "[I".
	 */
	private String signature;
	
	/**
	 * Original (BCEL's) type representation.
	 */
	private Type bcelType;
	
	/**
	 * Single element's (bmllib's) type.
	 */
	private JavaType1 type;

	/**
	 * A standard constructor.
	 * 
	 * @param signature - a BCEL's type signature. Can be
	 * 		obtained using {@link Type#getSignature()} method.
	 */
	public JavaArrayType(String signature) {
		this.signature = signature;
		bcelType = Type.getType(signature);
		if (bcelType instanceof ArrayType) {
			ArrayType at = (ArrayType) bcelType;
			Type et = at.getElementType();
			String subsig = et.getSignature();
			this.type = JavaType1.getJavaType(subsig);
		}
	}

	@Override
	public int compareTypes(JavaType1 type) {
		if (type == JavaReferenceType.ANY)
			return TYPES_EQUAL;
		if (type instanceof JavaArrayType) {
			JavaArrayType rt = (JavaArrayType) type;
			if (signature.equals(rt.getSignature()))
				return TYPES_EQUAL;
		}
		return TYPES_UNRELATED;
	}

	@Override
	protected String printCode1(BMLConfig conf) {
		return type.printCode(conf) + "[]";
	}

	@Override
	public String toString() {
		return signature;
	}

	/**
	 * @return Type's (BCEL) signature, eg. "[I".
	 */
	public String getSignature() {
		return signature;
	}

	/**
	 * Original (BCEL's) type representation.
	 */
	public Type getBcelType() {
		return bcelType;
	}

	/**
	 * @return Single element's (bmllib's) type.
	 */
	public JavaType1 getSingleType() {
		return type;
	}

}
