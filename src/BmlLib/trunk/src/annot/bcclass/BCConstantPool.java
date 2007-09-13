package annot.bcclass;

import java.io.ByteArrayInputStream;
import java.io.ByteArrayOutputStream;
import java.io.DataInputStream;
import java.io.DataOutputStream;
import java.io.IOException;
import java.util.Vector;

import org.apache.bcel.classfile.Attribute;
import org.apache.bcel.classfile.Constant;
import org.apache.bcel.classfile.ConstantPool;
import org.apache.bcel.classfile.ConstantUtf8;
import org.apache.bcel.classfile.JavaClass;
import org.apache.bcel.classfile.Unknown;
import org.apache.bcel.generic.ConstantPoolGen;

import annot.io.ConstantPoolReader;
import annot.io.ReadAttributeException;
import annot.textio.IDisplayStyle;

public class BCConstantPool {

	private Vector<Constant> constants;
	private int initialSize;

	public BCConstantPool(JavaClass jc) throws ReadAttributeException {
		constants = new Vector<Constant>();
		ConstantPoolGen cpg = new ConstantPoolGen(jc.getConstantPool());
		addStandardConstants(cpg);
		jc.setConstantPool(cpg.getFinalConstantPool());
		ConstantPool cp = jc.getConstantPool();
		initialSize = cp.getLength();
		for (int i = 0; i < initialSize; i++)
			constants.add(cp.getConstant(i));
		Attribute[] attrs = jc.getAttributes();
		byte[] bytes = null;
		for (int i = 0; i < attrs.length; i++)
			if (attrs[i] instanceof Unknown) {
				Unknown ua = (Unknown) attrs[i];
				if (IDisplayStyle.__second_cp.equals(ua.getName()))
					bytes = ua.getBytes();
			}
		if (bytes != null) {
			MLog.putMsg(MLog.PNotice, "second constant pool detected.");
			DataInputStream file = new DataInputStream(
					new ByteArrayInputStream(bytes));
			try {
				int size = file.readUnsignedShort();
				for (int i = 0; i < size; i++) {
					Constant c = ConstantPoolReader.readConstant(file);
					constants.add(c);
				}
			} catch (IOException e) {
				throw new ReadAttributeException(
						"error while reading second constant pool");
			}
		}
	}

	private void addStandardConstants(ConstantPoolGen cpg) {
		cpg.addUtf8(IDisplayStyle.jt_int);
		cpg.addUtf8(IDisplayStyle.__assertTable);
		cpg.addUtf8(IDisplayStyle.__classInvariant);
		cpg.addUtf8(IDisplayStyle.__mspec);
		cpg.addUtf8(IDisplayStyle.__second_cp);
	}

	public void addConstant(Constant c) {
		constants.add(c);
	}

	public Constant getConstant(int i) {
		return constants.elementAt(i);
	}

	public Constant searchForString(String str) {
		int pos = findConstant(str);
		if (pos == -1)
			return null;
		return getConstant(pos);
	}

	public int findConstant(String cdata) {
		int n = constants.size();
		for (int i = 0; i < n; i++) {
			Constant c = constants.elementAt(i);
			if (c instanceof ConstantUtf8) {
				ConstantUtf8 uc8 = (ConstantUtf8) c;
				if (cdata.equals(uc8.getBytes()))
					return i;
			}
		}
		return -1;
	}

	private String printElement(int i) {
		Constant c = constants.elementAt(i);
		if (c == null)
			return "";
		return ((i < 100) ? " " : "") + ((i < 10) ? " " : "") + i + ": "
				+ c.toString() + "\n";
	}

	public String printCode() {
		String code = "**** primary constant pool ****\n";
		for (int i = 0; i < initialSize; i++)
			code += printElement(i);
		code += "*** secondary constant pool ****\n";
		int n = constants.size();
		for (int i = initialSize; i < n; i++)
			code += printElement(i);
		return code;
	}

	public void save(JavaClass jc) throws IOException {
		int n = constants.size();
		Constant[] carr = new Constant[initialSize];
		for (int i = 0; i < initialSize; i++)
			carr[i] = constants.elementAt(i);
		jc.getConstantPool().setConstantPool(carr);
		ByteArrayOutputStream baos = new ByteArrayOutputStream();
		DataOutputStream file = new DataOutputStream(baos);
		file.writeShort(n - initialSize);
		for (int i = initialSize; i < n; i++)
			constants.elementAt(i).dump(file);
		ConstantPool cp = jc.getConstantPool();
		int nameIndex = findConstant(IDisplayStyle.__second_cp);
		int length = file.size();
		byte[] bytes = baos.toByteArray();
		Unknown scp = new Unknown(nameIndex, length, bytes, cp);
		Attribute[] atab = BCClass.addAttribute(jc.getAttributes(), scp);
		jc.setAttributes(atab);
	}

	public int size() {
		return constants.size();
	}

}
