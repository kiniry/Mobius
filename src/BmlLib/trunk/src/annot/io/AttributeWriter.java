package annot.io;

import org.apache.bcel.classfile.Unknown;

import annot.attributes.IBCAttribute;
import annot.bcclass.BCClass;
import annot.bcclass.BCMethod;
import annot.bcclass.MLog;
import annot.constants.BCConstant;
import annot.constants.BCConstantUtf8;

public class AttributeWriter {

	private BCClass bcc;
	private BCMethod bcm;
	private byte[] output;
	private int pos;

	public AttributeWriter(BCClass bcc) {
		this.bcc = bcc;
	}

	public AttributeWriter(BCMethod bcm) {
		this.bcc = bcm.bcc;
		this.bcm = bcm;
	}

	public Unknown writeAttribute(IBCAttribute attr) {
		MLog.putMsg(MLog.PInfo, "    writing attribute: " + attr.getName());
		output = new byte[4];
		pos = 0;
		attr.save(this);
		byte[] bytes = new byte[pos];
		for (int i = 0; i < pos; i++)
			bytes[i] = output[i];
		return new Unknown(attr.getIndex(), pos, bytes, bcc.jc
				.getConstantPool());
	}

	private void grow(int n) {
		if (pos + n > output.length) {
			byte[] arr = new byte[output.length * 2];
			for (int i = 0; i < output.length; i++)
				arr[i] = output[i];
			output = arr;
		}
	}

	public void writeByte(int b) {
		grow(1);
		output[pos] = (byte) (b & 0xff);
		pos++;
	}

	public void writeShort(int s) {
		grow(2);
		output[pos] = (byte) ((s >> 8) & 0xff);
		output[pos + 1] = (byte) (s & 0xff);
		pos += 2;
	}

	public void writeInt(int i) {
		grow(4);
		output[pos] = (byte) ((i >> 24) & 0xff);
		output[pos + 1] = (byte) ((i >> 16) & 0xff);
		output[pos + 2] = (byte) ((i >> 8) & 0xff);
		output[pos + 3] = (byte) (i & 0xff);
		pos += 4;
	}

	public void writeAttributeCount(int s) {
		writeShort(s);
	}

	public void writeUtf8(String str) {
		int l = str.length();
		if (l > 255)
			throw new RuntimeException("Uft constant too long!");
		grow(l + 1);
		writeByte(l);
		for (int i = 0; i < l; i++)
			writeByte((byte) str.charAt(i));
	}

	public int findConstant(String cname) {
		BCConstant c = bcc.cp.findConstant(cname);
		if (c == null) {
			BCConstantUtf8 bccu8 = new BCConstantUtf8(bcc.cp, cname);
			bcc.cp.addConstant(bccu8);
			return bccu8.getIndex();
		}
		return c.getIndex();
	}

}
