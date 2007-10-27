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

/**
 * This class represents extended constant pool, that contains
 * all constants from original (BCEL) constant pool and
 * constants from second constant pool. Second constant pool
 * is stored as an class attribute in .class file.
 * Constants stored here are ordinary, BCEL's Constants.
 * 
 * @author tomekb
 */
public class BCConstantPool {

	/**
	 * Constant array.
	 */
	private Vector<Constant> constants;

	/**
	 * Number of constants in main (BCEL's) constant pool.
	 */
	private int initialSize;

	/**
	 * JavaClass related with it's primary constantPool,
	 * used for {@link #reset()} method.
	 */
	private JavaClass jc;
	
	/**
	 * A standard constructor, from JavaClass. It inserts
	 * constants from ordinary constant pool first, and
	 * then from secons constant pool attribute.
	 * 
	 * @param jc - JavaClass to initialize from.
	 * @throws ReadAttributeException - if second constant
	 * 		pool attribute format is invalid.
	 */
	public BCConstantPool(JavaClass jc) throws ReadAttributeException {
		this.jc = jc;
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

	/**
	 * Adds standard constants (eg. attribute names) to the
	 * primary (BCEL) constant pool. This should be called only
	 * between loading primary and secondary constant pool.
	 * 
	 * @param cpg - BCEL's constant pool generator,
	 * 		from JavaClass.
	 */
	private void addStandardConstants(ConstantPoolGen cpg) {
		cpg.addUtf8(IDisplayStyle.jt_int);
		cpg.addUtf8(IDisplayStyle.__assertTable);
		cpg.addUtf8(IDisplayStyle.__classInvariant);
		cpg.addUtf8(IDisplayStyle.__mspec);
		cpg.addUtf8(IDisplayStyle.__second_cp);
		cpg.addUtf8(IDisplayStyle.__loopSpecTable);
	}

	/**
	 * Reinitializes constant pool from it's JavaClass'es
	 * primary constant pool, removing all variables from
	 * secondary constant pool.
	 */
	public void reset() {
		MLog.putMsg(MLog.PProgress, "clearing second constant pool");
		constants = new Vector<Constant>();
		ConstantPoolGen cpg = new ConstantPoolGen(jc.getConstantPool());
		addStandardConstants(cpg);
		jc.setConstantPool(cpg.getFinalConstantPool());
		ConstantPool cp = jc.getConstantPool();
		initialSize = cp.getLength();
		for (int i = 0; i < initialSize; i++)
			constants.add(cp.getConstant(i));
	}
	
	/**
	 * Appends a constant to the second constant pool.
	 * 
	 * @param c - Constant to be added.
	 */
	public void addConstant(Constant c) {
		constants.add(c);
	}

	/**
	 * Gives a constant from constant pool. Constants from
	 * second constant pool have indexes starting from
	 * <code>initialSize</code>, while constants from primary
	 * constant pool have indexes from 0 to initialSize - 1.
	 * Can be used in loading from file only.
	 * 
	 * @param i - constant index
	 * @return i-th constant.
	 */
	public Constant getConstant(int i) {
		return constants.elementAt(i);
	}

	/**
	 * Searches for an Utf8Constant with data equal to
	 * <code>str</code> in both primary and secondary constant
	 * pools.
	 * 
	 * @param str - string to search for.
	 * @return matching Constant or null if no Constant
	 * 		could be found.
	 */
	public Constant searchForString(String str) {
		int pos = findConstant(str);
		if (pos == -1)
			return null;
		return getConstant(pos);
	}

	/**
	 * Searches for an Utf8Constant with data equal to
	 * <code>str</code> in both primary and secondary constant
	 * pools.
	 * 
	 * @param str - string to search for.
	 * @return index of matching Constant or -1 if no
	 * 		Constant could be found.
	 */
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

	/**
	 * Displays i-th constant like:
	 * 	i :  CONSTANT_Utf8[1]("Code")
	 * 
	 * @param i - constant's index.
	 * @return a String like described above.
	 */
	private String printElement(int i) {
		Constant c = constants.elementAt(i);
		if (c == null)
			return "";
		return ((i < 100) ? " " : "") + ((i < 10) ? " " : "") + i + ": "
				+ c.toString() + "\n";
	}

	/**
	 * Prints both constant pools.
	 * 
	 * @return Constant pools String representation.
	 */
	public String printCode() {
		String code = "**** primary constant pool ****\n";
		for (int i = 0; i < initialSize; i++)
			code += printElement(i);
		int n = constants.size();
		if (n == initialSize)
			return code;
		code += "*** secondary constant pool ****\n";
		for (int i = initialSize; i < n; i++)
			code += printElement(i);
		return code;
	}

	/**
	 * Saves both constant pools to given JavaClass
	 * (primary as an ordinary constant pool and secondary
	 * as an "second constant pool" class attribute).
	 * 
	 * @param jc - JavaClass to save to.
	 */
	public void save(JavaClass jc) {
		int n = constants.size();
		Constant[] carr = new Constant[initialSize];
		for (int i = 0; i < initialSize; i++)
			carr[i] = constants.elementAt(i);
		jc.getConstantPool().setConstantPool(carr);
		ByteArrayOutputStream baos = new ByteArrayOutputStream();
		DataOutputStream file = new DataOutputStream(baos);
		try {
			file.writeShort(n - initialSize);
			for (int i = initialSize; i < n; i++)
				constants.elementAt(i).dump(file);
		} catch (IOException e) {
			e.printStackTrace();
			throw new RuntimeException("io error in BCConstantPool.save()");
		}
		ConstantPool cp = jc.getConstantPool();
		int nameIndex = findConstant(IDisplayStyle.__second_cp);
		int length = file.size();
		byte[] bytes = baos.toByteArray();
		Unknown scp = new Unknown(nameIndex, length, bytes, cp);
		Attribute[] atab = BCClass.addAttribute(jc.getAttributes(), scp);
		jc.setAttributes(atab);
	}

	/**
	 * @return number of constants stored in both
	 * 		constant pools.
	 */
	public int size() {
		return constants.size();
	}

}
