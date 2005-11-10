/*
 * Created on Oct 1, 2004
 *
 * To change the template for this generated file go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
package test;

/**
 * @author mpavlova
 *
 * To change the template for this generated type comment go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
public class F {
	public int x;
	
	//@ensures x == 1;
	public int a() {
		x= 0;
		try{
			//@  loop_modifies i,x;
			//@  loop_invariant x==i; //tazi invarianta ne e viarna
			//@  decreases i;
			for(int i = 0; i <= 0; i++) {
				if (i == 0)  {
					x = 1;
				} else if ( i == 1) {
					x = 2 ;
				} 
			}
			
		} catch (Exception _e) {
			_e.printStackTrace() ;
		}
		return x;
	}
}
