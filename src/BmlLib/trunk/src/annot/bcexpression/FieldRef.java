package annot.bcexpression;

import org.apache.bcel.classfile.ConstantFieldref;
import org.apache.bcel.classfile.ConstantNameAndType;
import org.apache.bcel.classfile.ConstantUtf8;

import annot.bcclass.BCConstantPool;
import annot.io.AttributeReader;
import annot.io.AttributeWriter;
import annot.io.Code;
import annot.io.ReadAttributeException;
import annot.textio.BMLConfig;
import annot.textio.Priorities;

/**
 * This class represents field reference occurence.
 * One <code>FieldRef</code> per one field reference
 * occurence.
 * 
 * @author tomekb
 */
public class FieldRef extends OldExpression {

	/**
	 * Index of FieldRef constant in constant pool.
	 * It's assumed that it won't change.
	 */
	private int cpIndex;
	
	/**
	 * type of the field.
	 */
	private JavaType1 type;
	
	/**
	 * name of the field.
	 */
	private String name;
	
	/**
	 * A standard constructor.
	 * 
	 * @param cp - Constant pool containing BCEL's
	 * 		<code>ConstantFieldRef</code> constant.
	 * 		FieldRef must be related with index
	 * 		in primary constant pool.
	 * @param cpIndex - index in <code>cp</code> where
	 * 		BCEL's <code>ConstantFieldRef</code> constant
	 * 		is beeing held.
	 */
	public FieldRef(boolean isOld, BCConstantPool cp, int cpIndex) {
		super(Code.FIELD_REF, isOld);
		loadName(cp, cpIndex);
	}

	/**
	 * A constructor from AttributeReader.
	 * 
	 * @param ar - input stream to load from,
	 * @param root - type of expression (last byte read
	 * 		from <code>ar</code>).
	 * @throws ReadAttributeException - if remaining stream
	 * 		in <code>ar</code> doesn't represent proper
	 * 		position in constant pool.
	 */
	public FieldRef(AttributeReader ar, int root)
			throws ReadAttributeException {
		super(ar, root);
	}

	/**
	 * A 'getInstance' method; searches for proper BCEL's
	 * <code>ConstantFieldRef</code> constant in given
	 * constant pool.
	 * 
	 * @param cp - constant pool to search in,
	 * @param name - name of the constant to be searched for.
	 * @return A new <code>FieldRef</code> insatnce,
	 * 		with name equal to the given one, or <b>null</b>
	 * 		in no proper constant could be found
	 * 		in <code>cp</code>.
	 */
	public static FieldRef getFieldOfName(boolean old, BCConstantPool cp, String name) {
		for (int i=0; i<cp.size(); i++) {
			if (cp.getConstant(i) == null)
				continue;
			if (!(cp.getConstant(i) instanceof ConstantFieldref))
				continue;
			ConstantFieldref cfr = (ConstantFieldref)cp.getConstant(i);
			ConstantNameAndType cnt = (ConstantNameAndType)cp.getConstant(cfr.getNameAndTypeIndex());
			ConstantUtf8 cu8 = (ConstantUtf8)cp.getConstant(cnt.getNameIndex());
			String cname = cu8.getBytes();
			if (cname.equals(name))
				return new FieldRef(old, cp, i);
		}
		return null;
	}

	/**
	 * Loads name and type from constant pool.
	 * 
	 * @param cp - constant pool to load from,
	 * @param cpIndex - index of BCEL's
	 * 		<code>ConstantFieldRef</code> constant,
	 * 		representing this field.
	 */
	private void loadName(BCConstantPool cp, int cpIndex) {
		this.cpIndex = cpIndex;
		ConstantFieldref cfr = (ConstantFieldref)cp.getConstant(cpIndex);
		ConstantNameAndType cnt = (ConstantNameAndType)cp.getConstant(cfr.getNameAndTypeIndex());
		ConstantUtf8 cu8 = (ConstantUtf8)cp.getConstant(cnt.getNameIndex());
		name = cu8.getBytes();
		ConstantUtf8 signature = (ConstantUtf8)cp.getConstant(cnt.getSignatureIndex());
		type = JavaType1.getJavaType(signature.getBytes());
	}
	
	@Override
	protected JavaType1 checkType2() {
		return type;
	}

	@Override
	protected int getPriority() {
		return Priorities.LEAF;
	}

	@Override
	public JavaType1 getType1() {
		return type;
	}

	@Override
	protected String printCode1(BMLConfig conf) {
		return isOld() ? ("old_" + name) : name;
	}

	@Override
	protected void read(AttributeReader ar, int root)
			throws ReadAttributeException {
		int cpIndex = ar.readShort();
		try {
			loadName(ar.getConstantPool(), cpIndex);
		} catch (ClassCastException e) {
			throw new ReadAttributeException("invalid position in constant pool: " + cpIndex);
		} catch (NullPointerException n) {
			throw new ReadAttributeException("invalid position in constant pool: " + cpIndex);
		}
	}

	@Override
	public String toString() {
		return type + " " + (isOld() ? ("old_" + name) : name);
	}

	@Override
	public void write(AttributeWriter aw) {
		aw.writeByte(getConnector());
		aw.writeShort(cpIndex);
	}

}
