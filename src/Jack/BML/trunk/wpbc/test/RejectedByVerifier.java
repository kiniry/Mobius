/*
 * Created on Jan 28, 2005
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
public class RejectedByVerifier {
	public static int m(boolean b) {
		int i;
		try {
			if (b) return 1;
			i =2 ;
		} finally {
			if (b) i =3;
		}
		return i;
	}
	
	public static void main(String[] args) {
		m(true);
	}
}
