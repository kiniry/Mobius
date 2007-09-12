package annot.attributes;

import java.util.Vector;

import annot.bcclass.BCConstantPool;
import annot.constants.BCConstant;
import annot.constants.BCConstantUtf8;
import annot.io.AttributeReader;
import annot.io.AttributeWriter;
import annot.io.Code;
import annot.io.ReadAttributeException;
import annot.textio.IDisplayStyle;

public class SecondConstantPool implements IBCAttribute {

	private BCConstantPool cp1;
	private Vector<BCConstant> constants;

	public SecondConstantPool(BCConstantPool cp1) {
		this.cp1 = cp1;
		this.constants = new Vector<BCConstant>();
	};

	public void addConstant(BCConstant c) {
		constants.add(c);
	}

	public BCConstant getAt(int i) {
		return constants.elementAt(i);
	}

	public int size() {
		return constants.size();
	}

	public void clear() {
		constants.clear();
		cp1.currentSize = cp1.initialSize;
	}

	public int getIndex() {
		return cp1.findConstant(getName()).getIndex();
	}

	public String getName() {
		return IDisplayStyle.__second_cp;
	}

	public void load(AttributeReader ar) throws ReadAttributeException {
		int n = ar.readShort();
		cp1.currentSize += n;
		for (int i = 0; i < n; i++) {
			int b = ar.readByte();
			switch (b) {
			case Code.CONSTANT_UTF8:
				BCConstantUtf8 bccu8 = new BCConstantUtf8(cp1, cp1.initialSize
						+ i, ar);
				addConstant(bccu8);
				break;
			default:
				throw new ReadAttributeException("Invalid constant type");
			}
		}
	}

	public void save(AttributeWriter aw) {
		int n = constants.size();
		aw.writeShort(n);
		for (int i = 0; i < n; i++)
			constants.get(i).save(aw);
	}

}
