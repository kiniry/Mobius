package annot.bcclass;

import org.apache.bcel.classfile.Method;

public class BMLConfig {
	private	BCConstantPool cp;
	public Method currMethod;
	public boolean goControlPrint = false;
	
	public BMLConfig(BCConstantPool cp) {
		this.cp = cp;
	}
	
	public BCConstantPool getConstantPool() {
		return cp;
	}
}
