/*
 * Created on Jan 27, 2005
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
public class ExampleBV {
	
	public static boolean k() {
		return true;
	}
	
	public static void m(boolean b) {
		while (b ) {
			try{
				b = k();
			} finally {
				if (b) continue;
			}
		}
	}

	public static void main(String[] args) {
			m( true );
			/*System.out.println(" ExampleBV" );*/
	}
}
