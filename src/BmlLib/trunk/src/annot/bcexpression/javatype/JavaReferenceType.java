package annot.bcexpression.javatype;

import annot.io.AttributeWriter;
import annot.io.Code;
import annot.textio.BMLConfig;

/**
 * This class describes any non-basic Java type.
 * It only stores type's signature.
 * 
 * @author tomekb
 */
public class JavaReferenceType extends JavaType {

	/**
	 * A type's signature. It can be any String, currently
	 * it's value is never parsed into other structures
	 * in this library.
	 */
	private String signature;
	
	/**
	 * A standard constructor.
	 * 
	 * @param signature - type's signature.
	 */
	public JavaReferenceType(String signature) {
		this.signature = signature;
	}

	/**
	 * Type of null, for example.
	 */
	public static final JavaReferenceType ANY = new JavaReferenceType("Object");

	/**
	 * Returns this type's signature as a String
	 * (the same String as given in constructor).
	 */
	@Override
	protected String printCode1(BMLConfig conf) {
		return signature;
	}

	@Override
	public String toString() {
		return signature;
	}

	@Override
	public void write(AttributeWriter aw) {
		aw.writeByte(Code.JAVA_TYPE);
		int cpIndex = aw.findConstant(signature);
		aw.writeShort(cpIndex);
	}

	@Override
	public int compareTypes(JavaType type) {
		if (signature == null)
			throw new RuntimeException("signature == null, what does it mean?");
		if (type == ANY)
			return TYPES_EQUAL;
		if (type instanceof JavaReferenceType) {
			JavaReferenceType rt = (JavaReferenceType) type;
			if (signature.equals(rt.getSignature()))
				return TYPES_EQUAL;
			//TODO check for subtypes
		}
		return TYPES_UNRELATED;
	}

	public String getSignature() {
		return signature;
	}

}
