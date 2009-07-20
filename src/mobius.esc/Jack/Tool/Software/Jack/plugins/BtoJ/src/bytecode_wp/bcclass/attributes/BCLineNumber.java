/*
 * Created on Sep 3, 2004
 *
 * To change the template for this generated file go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
package bytecode_wp.bcclass.attributes;

/**
 * @author mpavlova
 *
 * To change the template for this generated type comment go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
public class BCLineNumber {
	private int startPC;
	private int srcLine;
	
	public BCLineNumber(int startPC, int srcLine) {
		this.startPC = startPC;
		this.srcLine = srcLine;	
	}
	
	
	
	

	/**
	 * @return
	 */
	public int getSrcLine() {
		return srcLine;
	}

	/**
	 * @return
	 */
	public int getStartPC() {
		return startPC;
	}

}
