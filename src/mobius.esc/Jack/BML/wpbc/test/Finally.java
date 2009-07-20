/*
 * Created on Jan 29, 2005
 *
 * TODO To change the template for this generated file go to
 * Window - Preferences - Java - Code Style - Code Templates
 */
package test;

/**
 * @author Mariela
 *
 * TODO To change the template for this generated type comment go to
 * Window - Preferences - Java - Code Style - Code Templates
 */
public class Finally {
	
	public void m() {
		int[] i;
		try {
			i = new int[3];
			i[0] = 1;
		} finally {
			i = null; 
		}
	}
 
}
