/*
 * Created on Feb 23, 2004
 *
 * To change the template for this generated file go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
package test;
import constants.*;
/**
 * @author mpavlova
 *
 * To change the template for this generated type comment go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
public class Test {
	boolean BOOL;
	int i,j;
	BCConstant constant;
	 
	Object arr[] = new Object[3]; 
	
	public void m0() {
		int i = 0;
		while (BOOL) {
			i = i+1;
		} 
	}
	
	public void m1() {
		int i = 0;
		if (BOOL ) {
			i++;
		} else if (!BOOL) {
			while(BOOL) {
				i++;
			}
			i--;
		}
	}
	
	void m2()  {
		
		while (BOOL) {
			if ( i+1 == 3 ) {
				i++;
				break;
			}
			i = 0;
		}
		i++;
	}
	
	
	 //	@requires true;
	 //@ensures i >2;
	public  void m3() {
		 
		  if ( i == 3) {
			  //getRef();
			  i = 5;
		  }  else {
			  //array();
			  i = 3;
		  }
 	 }
	
	public void cast() {
		BCConstantClass _class = (BCConstantClass)constant;
	}
	
	/**
	 * 
	 * @throws NullPointerException
	 * exsures NullPointerException
	 */
	public void _throw() throws NullPointerException {
		Object o = new Object();
		int i = 0 ;
		
		try {
			i++;
			 new NullPointerException();
			while ( i < 2 ) {
				i++;
			}
			throw new  NullPointerException();
		} catch (NullPointerException e) {
			i = 100;
			return;
		} finally {
			i = 0;
		}
	}
	
	//@ j > i;
	public void sub() {
		j = i;
		i = i - 3;
	}
	
	public void array() {
		arr[1] = this;
	}
}
