/*
 * Created on 8 mars 2004
 *
 * To change the template for this generated file go to
 * Window - Preferences - Java - Code Generation - Code and Comments
 */
package constants;

import org.apache.bcel.classfile.ConstantCP;
import org.apache.bcel.classfile.ConstantNameAndType;
import org.apache.bcel.classfile.ConstantPool;
import org.apache.bcel.generic.ConstantPoolGen;
import org.apache.bcel.generic.Type;

/**
 * @author io
 *
 * To change the template for this generated type comment go to
 * Window - Preferences - Java - Code Generation - Code and Comments
 */
public class BCConstantRef extends BCConstant {
	private int classIndex;
	private int nameAndTypeIndex;
	
	public BCConstantRef() {
	}
	
	public BCConstantRef(ConstantCP _cp, int _cpIndex){
		this(_cp.getClassIndex(), _cp.getNameAndTypeIndex(),  _cpIndex);
	}
	
	public BCConstantRef(int _classIndex, int _nameAndTypeIndex ,int _cpIndex ) {
		super(_cpIndex);
		classIndex = _classIndex;
		nameAndTypeIndex = _nameAndTypeIndex;
	}
	
	public int getNameAndTypeIndex() {
		return nameAndTypeIndex;
	}
	
	public int getClassIndex() {
		return classIndex;
	}
	
	public String getSignature(ConstantPool _cp) {
		return ((ConstantNameAndType)_cp.getConstant(nameAndTypeIndex)).getSignature(_cp);
	}
}
