

/*
 * Created on Jan 24, 2005
 *
 * TODO To change the template for this generated file go to
 * Window - Preferences - Java - Code Style - Code Templates
 */
package test;

/**
 * @author mpavlova
 *
 * test to see if the pogs generated on source level take into account 
 * the  
 */
public class TestValue {
	
	//@ ensures \result == true; 
	public boolean testIfValue() {
		boolean _true = true;
		if (_true) {
			return true;
		} 
		return false;
	}
}
