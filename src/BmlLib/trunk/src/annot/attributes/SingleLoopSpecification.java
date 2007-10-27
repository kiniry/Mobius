package annot.attributes;

import org.apache.bcel.generic.InstructionHandle;

import annot.bcclass.BCMethod;
import annot.bcexpression.ExpressionRoot;
import annot.io.AttributeReader;
import annot.io.AttributeWriter;
import annot.io.ReadAttributeException;
import annot.textio.BMLConfig;

public class SingleLoopSpecification extends InCodeAttribute {

	public SingleLoopSpecification(BCMethod m, InstructionHandle ih, int minor) {
		super(m, ih, minor);
		// TODO Auto-generated constructor stub
	}

	@Override
	protected int aType() {
		// TODO Auto-generated method stub
		return 0;
	}

	@Override
	protected void load(AttributeReader ar) throws ReadAttributeException {
		// TODO Auto-generated method stub

	}

	@Override
	protected String printCode1(BMLConfig conf) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	protected void saveSingle(AttributeWriter aw) {
		// TODO Auto-generated method stub

	}

	@Override
	public ExpressionRoot[] getAllExpressions() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public String toString() {
		// TODO Auto-generated method stub
		return null;
	}

}
