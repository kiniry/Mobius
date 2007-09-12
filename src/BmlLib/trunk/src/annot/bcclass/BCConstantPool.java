package annot.bcclass;

import org.apache.bcel.classfile.Constant;
import org.apache.bcel.classfile.ConstantPool;
import org.apache.bcel.classfile.ConstantUtf8;
import org.apache.bcel.generic.ConstantPoolGen;

import annot.attributes.SecondConstantPool;
import annot.constants.BCConstant;
import annot.constants.BCConstantUtf8;
import annot.constants.UnknownConstant;
import annot.textio.BMLConfig;
import annot.textio.IDisplayStyle;

public class BCConstantPool {
	private BCClass bcc;
	private ConstantPoolGen cpg;
	private BCConstant[] constants;
	public int initialSize;
	public int currentSize;
	public SecondConstantPool scp;

	public BCConstantPool(BCClass bcc, ConstantPoolGen cpg) {
		this.bcc = bcc;
		this.cpg = cpg;
		this.scp = new SecondConstantPool(this);
		addStandardConstants();
		update();
		cpg = this.cpg;
		currentSize = initialSize = cpg.getSize();
		constants = new BCConstant[initialSize];
		for (int i = 0; i < initialSize; i++)
			constants[i] = convert(cpg.getConstant(i), i);
	}

	private void update() {
		ConstantPool cp = cpg.getFinalConstantPool();
		bcc.jc.setConstantPool(cp);
		cpg = new ConstantPoolGen(cp);
	}

	private void addStandardConstants() {
		cpg.addUtf8(IDisplayStyle.__mspec);
		cpg.addUtf8(IDisplayStyle.__classInvariant);
		cpg.addUtf8(IDisplayStyle.__assertTable);
		cpg.addUtf8(IDisplayStyle.__second_cp);
		cpg.addUtf8(IDisplayStyle.jt_int);
	}

	private BCConstant convert(Constant c, int index) {
		if (c == null)
			return null;
		if (c instanceof ConstantUtf8)
			return new BCConstantUtf8(this, (ConstantUtf8) c, index);
		// TODO: make BCConstant abstract and throw an exception here
		return new UnknownConstant(this, c, index);
	}

	public String printCode(BMLConfig conf) {
		String code = "------ BCConstantPool ------\n";
		for (int i = 0; i < initialSize; i++)
			if (constants[i] != null)
				code += i + ": " + ((i < 10) ? " " : "")
						+ constants[i].printCode(conf) + "\n";
		code += "---- SecondConstantPool ----\n";
		for (int i = initialSize; i < currentSize; i++)
			code += i + ": " + ((i < 10) ? " " : "") + getAt(i).printCode(conf);
		return code;
	}

	public BCConstantUtf8 findConstant(String value) {
		for (int i = 0; i < currentSize; i++) {
			BCConstant c = getAt(i);
			if (c instanceof BCConstantUtf8) {
				BCConstantUtf8 bccu8 = (BCConstantUtf8) c;
				if (bccu8.data.equals(value))
					return bccu8;
			}
		}
		return null;
	}

	public BCConstant getAt(int i) {
		if (i >= currentSize)
			return null;
		if (i >= initialSize)
			return scp.getAt(i - initialSize);
		return constants[i];
	}

	public void addConstant(BCConstant c) {
		scp.addConstant(c);
		c.cpIndex = currentSize;
		currentSize++;
	}

	public int size() {
		return currentSize;
	}

}
