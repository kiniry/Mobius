/*
 * Created on Mar 4, 2004
 *
 * To change the template for this generated file go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
package bcclass;

import org.apache.bcel.classfile.LocalVariable;
import org.apache.bcel.generic.Type;

/**
 * @author mpavlova
 *
 * To change the template for this generated type comment go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
public class BCLocalVariable {
	private int index;
	private int start_pc;
	private int length;
	private int name_index;
	private int signature_index;

	private Type type;

	public BCLocalVariable(int _index, Type _type) {
		type = _type;
		index = _index;
	}

	public BCLocalVariable(
		int _start_pc,
		int _length,
		int _name_index,
		int _signature_index,
		int _index) {
		//this(_index);
		index = _index;
		start_pc = _start_pc;
		length = _length;
		name_index = _name_index;
		signature_index = _signature_index;
	}

	public BCLocalVariable(LocalVariable lv) {
		//lv.get
		this(
			lv.getStartPC(),
			lv.getLength(),
			lv.getNameIndex(),
			lv.getSignatureIndex(),
			lv.getIndex());
	}

	/**
	 * @return
	 */
	public int getIndex() {
		return index;
	}

	/**
	 * @return
	 */
	public int getLength() {
		return length;
	}

	/**
	 * @return
	 */
	public int getName_index() {
		return name_index;
	}

	/**
	 * @return
	 */
	public int getSignature_index() {
		return signature_index;
	}

	/**
	 * @return
	 */
	public int getStart_pc() {
		return start_pc;
	}

}
