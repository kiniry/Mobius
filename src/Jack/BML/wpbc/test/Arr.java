/*
 * Created on Dec 8, 2004
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
public class Arr {

	
	//@ ensures \result == 0;
	public static int run() {
		int[] o1 = new int[5];
		int a[] = o1;
		int[] o2 = a;
		a[0] = 1;
		if (o2[0] == o1[0]) {
			return 0;
		}
		return 1;
	}
}
