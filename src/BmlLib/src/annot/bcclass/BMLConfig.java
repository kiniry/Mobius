package annot.bcclass;

public class BMLConfig {
	private	BCConstantPool cp;
	
	public BMLConfig(BCConstantPool cp) {
		this.cp = cp;
	}
	
	public BCConstantPool getConstantPool() {
		return cp;
	}
}
