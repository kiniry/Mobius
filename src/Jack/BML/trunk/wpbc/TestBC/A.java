
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
	
	private String str;
	
	private A[] arr;
	
	public A (){
		System.out.println(m());	
	}
	
	

	public void  GETSTATIC() {
		//a = C.a; 
	}
	
	
	public String GETFIELD() {
		return str;
	}

	public int m(){
		return 1;
	} 

	public void testNEWARR() {		
		A[] a = new A[3];
	}
	
	public void testCheckCast(A a) {
		B b  = (B)a ;
	}
	
	
	public void newInstance() {
		a = new B();
	}
	
	public  void n() {
		try{
		
			int i  ;
	  		i =	a.m();
	  		
	  		throw new NullPointerException();
		} catch (NullPointerException e) {
		
		}
	}

	public static int s() {
		return 1;
	}
	

	
}
