/*
 * Created on 4 mai 2004
 *
 * To change the template for this generated file go to
 * Window - Preferences - Java - Code Generation - Code and Comments
 */
package test;

/**
 * @author io
 *
 * To change the template for this generated type comment go to
 * Window - Preferences - Java - Code Generation - Code and Comments
 */
public class TestRef {
	
	public static void main(String[] args) {
		A a = new A();
		A[] arr = a.getArray() ;
		
		arr[0] = new A();
		arr[1] = new A();
		arr[0].j = 3;
		
		boolean eq = arr[0].getClass() == arr[1].getClass() ? true : false; 
		System.out.println("arr[0].getClass() == arr[1].getClass() is"  + eq);
		System.out.println("a.array[0].j == arr[0].j is " + (a.array[0].j == arr[0].j));
	}
}
