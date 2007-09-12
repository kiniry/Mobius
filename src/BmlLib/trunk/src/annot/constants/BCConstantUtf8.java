package annot.constants;

import org.apache.bcel.classfile.ConstantUtf8;

import annot.bcclass.BCConstantPool;
import annot.io.AttributeReader;
import annot.io.AttributeWriter;
import annot.io.Code;
import annot.io.ReadAttributeException;
import annot.textio.BMLConfig;

public class BCConstantUtf8 extends BCConstant {

	public String data;

	public BCConstantUtf8(BCConstantPool bcp, ConstantUtf8 c, int cpIndex) {
		super(bcp, c, cpIndex);
		this.data = c.getBytes();
	}

	public BCConstantUtf8(BCConstantPool bcp, int cpIndex, AttributeReader ar)
			throws ReadAttributeException {
		super(bcp, cpIndex, ar);
	}

	public BCConstantUtf8(BCConstantPool bcp, String data) {
		super(bcp, null, -1);
		this.data = data;
	}

	@Override
	public String printCode(BMLConfig conf) {
		return data;
	}

	@Override
	public void load(AttributeReader ar) throws ReadAttributeException {
		data = ar.readUtf8();
	}

	@Override
	public void save(AttributeWriter aw) {
		aw.writeByte(Code.CONSTANT_UTF8);
		aw.writeUtf8(data);
	}

}
