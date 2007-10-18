package annot.bcexpression;

import annot.io.AttributeWriter;
import annot.io.Code;
import annot.textio.BMLConfig;

/**
 * This class describes any non-basic Java type.
 * It only stores type's signature.
 * 
 * @author tomekb
 */
public class JavaReferenceType extends JavaType1 {

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
	 * Returns this type's signature as a String
	 * (the same String as given in constructor).
	 */
	@Override
	protected String printCode1(BMLConfig conf) {
		return signature;
	}

	@Override
	public String toString() {
		return "JavaReferenceType: " + signature;
	}

	@Override
	public void write(AttributeWriter aw) {
		aw.writeByte(Code.JAVA_TYPE);
		int cpIndex = aw.findConstant(signature);
		aw.writeShort(cpIndex);
	}

}
