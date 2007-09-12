package annot.constants;

import org.apache.bcel.classfile.Constant;

import annot.bcclass.BCConstantPool;
import annot.io.AttributeReader;
import annot.io.AttributeWriter;
import annot.io.ReadAttributeException;
import annot.textio.BMLConfig;

public class UnknownConstant extends BCConstant {

	public UnknownConstant(BCConstantPool bcp, Constant c, int cpIndex) {
		super(bcp, c, cpIndex);
	}

	@Override
	public void load(AttributeReader ar) throws ReadAttributeException {
		throw new RuntimeException("cannot load constant stub");
	}

	@Override
	public String printCode(BMLConfig conf) {
		return toString();
	}

	@Override
	public void save(AttributeWriter aw) {
		throw new RuntimeException("cannot save constant stub");
	}

}
