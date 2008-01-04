package annot.attributes;

import org.apache.bcel.classfile.Constant;
import org.apache.bcel.classfile.ConstantUtf8;

import annot.bcexpression.BCExpression;
import annot.bcexpression.ExpressionRoot;
import annot.bcexpression.javatype.JavaReferenceType;
import annot.bcexpression.javatype.JavaType;
import annot.io.AttributeReader;
import annot.io.AttributeWriter;
import annot.io.ReadAttributeException;
import annot.textio.BMLConfig;
import annot.bcexpression.formula.AbstractFormula;

/**
 * This class represents method's exception type (throws
 * declaration) with condition in which such exception
 * can be thrown by this method.
 * 
 * @author tomekb
 */
public class Exsure {
//XXX shouldn't I attached here reference to describing method?

	/**
	 * Type of the exception declared.
	 */
	private JavaReferenceType excType;
	
	/**
	 * Postcondition that is ensured in case of throwing
	 * <code>excType</code> exception by this method.
	 */
	private ExpressionRoot<AbstractFormula> postcondition;
	
	/**
	 * A standard constructor.
	 * 
	 * @param excType - exception type,
	 * @param postcondition - postcondition exsures when
	 * 		<code>excType</code> exception is thrown
	 * 		by this method.
	 */
	public Exsure(JavaReferenceType excType, AbstractFormula postcondition) {
		this.excType = excType;
		this.postcondition = new ExpressionRoot<AbstractFormula>(this, postcondition);
	}

	/**
	 * A constructor from AttributeReader. Each exsures entry has the form
	 * <pre>
   * {
   *    u2 exception_index;
   *    formula_info exsures_formula;
   * }
   * </pre>
   *
	 * @param ar input stream to load from
	 * @throws ReadAttributeException if remaining stream in
	 * 		<code>ar</code> does not represent a correct Exsure
	 * 		attribute
	 */
	public Exsure(AttributeReader ar) throws ReadAttributeException {
    int cpindex = ar.readShort(); // read the exception index
    String name = ar.findString(cpindex); //interpret from the constant pool
		BCExpression expr = JavaType.getJavaType(name);
		if (!(expr instanceof JavaReferenceType))
			throw new ReadAttributeException("JavaType expected");
		this.excType = (JavaReferenceType)expr;
		this.postcondition = new ExpressionRoot<AbstractFormula>(this,
        ar.readFormula()); // read the exsures formula
	}
	
	/**
	 * Displays this exsure to a String.
	 * 
	 * @param conf - see {@link BMLConfig}.
	 * @return String representation of this excondition.
	 */
	public String printCode(BMLConfig conf) {
		String prefix = excType.printCode(conf) + ": ";
		return postcondition.printLine(conf, prefix);
	}
	
	/**
	 * Writes this exsure to AttributeWriter. The format in which we write is:
   * <pre>
   * {
   *    u2 exception_index;
   *    formula_info exsures_formula;
   * }
   * </pre>
	 * 
	 * @param aw - output stream to save to.
	 */
	public void writeSingle(AttributeWriter aw) {
		int cpindex = aw.findConstant(excType.getSignature());
    aw.writeShort(cpindex);
		postcondition.write(aw);
	}

	/**
	 * @return Type of the exception declared.
	 */
	public JavaReferenceType getExcType() {
		return excType;
	}

	/**
	 * @return Postcondition that is ensured in case
	 * 		of throwing <code>excType</code> exception
	 * 		by this method.
	 */
	public ExpressionRoot<AbstractFormula> getPostcondition() {
		return postcondition;
	}

}
