/*
 * Created on Mar 3, 2004
 *
 * To change the template for this generated file go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
package constants;

import org.apache.bcel.generic.Type;


/**
 * @author mpavlova
 *
 * To change the template for this generated type comment go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
public abstract class  BCConstant {
	private int cpIndex; 
	private byte tag;

	
	public BCConstant(int _cpIndex) {
		cpIndex = _cpIndex;
	}
	 
	public  int getCPIndex() {
		return cpIndex;
	}
	
	public String toString() {
		return null;
	}
	public byte getTag()  {
		return tag;
	}
	
	

}
