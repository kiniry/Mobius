
package TestBC;

/*
 * Created on Mar 22, 2004
 *
 * To change the template for this generated file go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */

/**
 * @author mpavlova
 *
 * To change the template for this generated type comment go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
public class A {
	
	private A a;
	public int m(){
		return 1;
	} 

	
	public void n() {
		try{
		
			int i  ;
	  		i =	a.m();
	  		throw new NullPointerException();
		} catch (NullPointerException e) {
		
		}
	}

}
