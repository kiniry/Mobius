/*
 * Created on Sep 20, 2004
 *
 * To change the template for this generated file go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
package test;

/**
 * @author mpavlova
 *
 * To change the template for this generated type comment go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
public class B {
	//@ invariant array != null;
	
	public B b;
	public int i;
	public int[] array;
	
	public B(int length , int j) { // allocates 1
		array = new int[length];
		array[j] = j ;
		i = j;
		A a = new A();//1
	}
	
	public B(int[] _array , int j) {
		_array = array;
		array[j] = j;
	}
		
	 //@ requires true;
	 //@ modifies \nothing; 
	 //@ ensures \result.array == this.array;
	 
	public B m2() {
		b = new B(array, i); // 1 unit 
		return b;
	}
	
	 //@ requires true;
	 //@ modifies b.b, b.array[*], b.b.array[1..2]; 
	 //@ ensures \result == b;
	 public B m3() {
		b.b =  new B(array, i );
		return b;
	}
}
