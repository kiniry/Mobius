/*
 * Created on Feb 3, 2005
 *
 * TODO To change the template for this generated file go to
 * Window - Preferences - Java - Code Style - Code Templates
 */
package test;

/**
 * @author mpavlova
 *
 * TODO To change the template for this generated type comment go to
 * Window - Preferences - Java - Code Style - Code Templates
 */
public class TestLoops {
	
	public void m() {
		int i = 0;
		do {
			do {
				for( int k = 0; k < i; k++) {
					k = 1;
				}
				i --;
			} while (i > 3 );
			i ++;
		} while ( i < 7 );
	}

}
