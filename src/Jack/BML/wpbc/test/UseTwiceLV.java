/*
 * Created on Jan 24, 2005
 *
 * TODO To change the template for this generated file go to
 * Window - Preferences - Java - Code Style - Code Templates
 */
package test;

/**
 * @author mpavlova
 * TODO To change the template for this generated type comment go to
 * Window - Preferences - Java - Code Style - Code Templates
 */
public class UseTwiceLV {
	
	public void m() {
		int i = 1;
		while ( true ) {
			A a = new A();
			System.out.println("Execute ok");
		}
	}
	
	public void infinitSubRoutine() {
		while (true) {
			try{
				m();
			} finally {
				continue;
			}
		} 
	}
	
	public void jumpInSbroutine() {
		try{
			m();
		} finally {
			int i = 0;
		}
	
	}

	public static void main(String[] a) {
		UseTwiceLV u = new UseTwiceLV();
		u.jumpInSbroutine();
		System.out.println("Execute ok");
	} 
}
