/*
 * Created on 17 sept. 2004
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
public class ReferenceTest {

	public static void setArr( int[] array) {
		/*int[] _arr;
		_arr = array;
		_arr[0] = 5;*/
		int _arr;
		_arr = array[0];
		_arr = 5;
	}
	
	public static void main(String[] args) {
		int[] m = new int[]{1, 2, 3};
		setArr( m);
		System.out.println(m[0]);
	
	}
}
