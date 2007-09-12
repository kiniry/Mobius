package annot.constants;

import org.apache.bcel.classfile.Constant;

import annot.bcclass.BCConstantPool;
import annot.io.AttributeReader;
import annot.io.AttributeWriter;
import annot.io.ReadAttributeException;
import annot.textio.BMLConfig;

public abstract class BCConstant {

	private Constant bcelConstant;
	public int cpIndex;

	public abstract String printCode(BMLConfig conf);

	public abstract void load(AttributeReader ar) throws ReadAttributeException;

	public abstract void save(AttributeWriter aw);

	public BCConstant(BCConstantPool bcp, Constant c, int cpIndex) {
		this.bcelConstant = c;
		this.cpIndex = cpIndex;
	}

	public BCConstant(BCConstantPool bcp, int cpIndex, AttributeReader ar)
			throws ReadAttributeException {
		this.cpIndex = cpIndex;
		load(ar);
	}

	public int getIndex() {
		return cpIndex;
	}

	@Override
	public String toString() {
		if (bcelConstant != null)
			return bcelConstant.toString();
		return "a constant from second constant pool";
	}

}
