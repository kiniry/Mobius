/*
 * Created on Apr 26, 2004
 *
 * To change the template for this generated file go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
package TestBC;

/**
 * @author mpavlova
 *
 * To change the template for this generated type comment go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
public class C {
	//static  A a = new B();
	
	
	public C( A a) {
		test(a);
	}
	
	public void test(A a) {
		System.out.println("in test(A a)");
	}
	
	public void test(B b) {
		System.out.println("in test(B b)");
	}
	
	public static void main(String[] args ) {
		C c  = new C(new B());
	}
}
