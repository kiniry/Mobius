package annot.io;

import org.apache.bcel.classfile.ConstantUtf8;
import org.apache.bcel.classfile.Unknown;

import annot.attributes.IBCAttribute;
import annot.bcclass.BCClass;
import annot.bcclass.BCMethod;
import annot.bcclass.MLog;

/**
 * This class is used to write BML attributes (of IBCAttribute type) to the
 * BCEL's Unkonwn attribute.
 * 
 * @author tomekb
 */
public class AttributeWriter {

	/**
	 * BCClass containing attributes to be written.
	 */
	private BCClass bcc;

	/**
	 * BCMethod containing attributes to be written.
	 */
	private BCMethod bcm;

	/**
	 * Output 'stream' to write attributes to. XXX should be replaced with
	 * Vector<byte>.
	 */
	private byte[] output;

	/**
	 * Position in the output stream.
	 */
	private int pos;

	/**
	 * A contructor for BCClass (to write class atributes).
	 * 
	 * @param bcc -
	 *            class containing attributes to be written.
	 */
	public AttributeWriter(BCClass bcc) {
		this.bcc = bcc;
	}

	/**
	 * A constructor for BCMethod (to write method attriutes).
	 * 
	 * @param bcm -
	 *            method containing attributes to be written.
	 */
	public AttributeWriter(BCMethod bcm) {
		this.bcc = bcm.getBcc();
		this.bcm = bcm;
	}

	/**
	 * Written given attribute (of IBCAttribute interface), creating BCEL's
	 * Unknown attribute.
	 * 
	 * @param attr -
	 *            Attribute to be written,
	 * @return Uknonwn attribute representing given attribute.
	 */
	public Unknown writeAttribute(IBCAttribute attr) {
		MLog.putMsg(MLog.PInfo, "    writing attribute: " + attr.getName());
		output = new byte[4];
		pos = 0;
		attr.save(this);
		byte[] bytes = new byte[pos];
		for (int i = 0; i < pos; i++)
			bytes[i] = output[i];
		return new Unknown(attr.getIndex(), pos, bytes, bcc.getJc()
				.getConstantPool());
	}

	/**
	 * Increases stream capacity twice, if nessesery.
	 * 
	 * @param n -
	 *            number of bytes that needs to be avaliable to write int the
	 *            stream.
	 */
	private void grow(int n) {
		if (pos + n > output.length) {
			byte[] arr = new byte[output.length * 2];
			for (int i = 0; i < output.length; i++)
				arr[i] = output[i];
			output = arr;
		}
	}

	/**
	 * Writes a byte to the stream.
	 * 
	 * @param b -
	 *            byte to be written.
	 */
	public void writeByte(int b) {
		grow(1);
		output[pos] = (byte) (b & 0xff);
		pos++;
	}

	/**
	 * Writes an short integer (2 bytes) to the stream.
	 * 
	 * @param b -
	 *            integer to be written (less than 2^15).
	 */
	public void writeShort(int s) {
		grow(2);
		output[pos] = (byte) ((s >> 8) & 0xff);
		output[pos + 1] = (byte) (s & 0xff);
		pos += 2;
	}

	/**
	 * Writes an integer (4 bytes) to the stream.
	 * 
	 * @param b -
	 *            integer to be written.
	 */
	public void writeInt(int i) {
		grow(4);
		output[pos] = (byte) ((i >> 24) & 0xff);
		output[pos + 1] = (byte) ((i >> 16) & 0xff);
		output[pos + 2] = (byte) ((i >> 8) & 0xff);
		output[pos + 3] = (byte) (i & 0xff);
		pos += 4;
	}

	/**
	 * Writes a attribute count (2 bytes) to the stream.
	 * 
	 * @param b -
	 *            attribute count to be written.
	 */
	public void writeAttributeCount(int s) {
		writeShort(s);
	}

	/**
	 * Searches for Utf8 constant in constant pool constaining given String,
	 * returning it's index. If it cannot be found, a new UtfConstant is created
	 * and appended to the second constant pool (and it's index is returned).
	 * 
	 * @param str -
	 *            String to search for.
	 * @return Index of Utf8 constant with given String.
	 */
	public int findConstant(String str) {
		int pos = bcc.getCp().findConstant(str);
		if (pos == -1) {
			ConstantUtf8 cu8 = new ConstantUtf8(str);
			bcc.getCp().addConstant(cu8);
			return bcc.getCp().size() - 1;
		}
		return pos;
	}

}
