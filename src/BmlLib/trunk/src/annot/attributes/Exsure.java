package annot.attributes;

import annot.bcexpression.BCExpression;
import annot.bcexpression.JavaReferenceType;
import annot.formula.AbstractFormula;
import annot.io.AttributeReader;
import annot.io.AttributeWriter;
import annot.io.ReadAttributeException;
import annot.textio.BMLConfig;

public class Exsure {

	private JavaReferenceType excType;
	private AbstractFormula postcondition;
	
	public Exsure(JavaReferenceType excType, AbstractFormula postcondition) {
		this.excType = excType;
		this.postcondition = postcondition;
	}

	public Exsure(AttributeReader ar) throws ReadAttributeException {
		BCExpression expr = ar.readExpression();
		if (!(expr instanceof JavaReferenceType))
			throw new ReadAttributeException("JavaType expected");
		this.excType = (JavaReferenceType)expr;
		this.postcondition = ar.readFormula();
	}
	
	public String printCode(BMLConfig conf) {
		String prefix = excType.printCode(conf) + ": ";
		return postcondition.printLine(conf, prefix);
	}
	
	public void writeSingle(AttributeWriter aw) {
		excType.write(aw);
		postcondition.write(aw);
	}

}
