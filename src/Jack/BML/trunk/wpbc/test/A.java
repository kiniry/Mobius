package test;

import org.apache.bcel.classfile.JavaClass;

public class A {
	public A b;
	public A arr[] = new A[5];
	/*
	//@ invariant b == null;
	*/
	
	//@ensures \result == b;
	public A testMethodInvokation() throws NullPointerException {
		b = b.testThisAccess(b, b);
		return b;
	}
	
	
	//@ requires true;
	//@ modifies arr[1..3];
	//@ ensures arr[1] == arr[2];
	public void modifyArray() {
		arr[0] = new A();
	}
	

	
	//@ requires true;
	//@ modifies this.b ;
	//@ ensures \result == this;
	//@ exsures (ArrayIndexOutOfBoundsException e) arr.length < 2;
	public A testThisAccess(A a1, A a2)  {
		/*try {*/
			a1.b.b = this;
/*			b = a1.b.b;*/
			arr = new A[2];
/*			arr = new A[2];*/
/*			arr = new A[3];*/
			a1 = new A();
			a2 = new A();
			B b = new B(2, 3); // allocates 2
			b.m2();
			return a1.b.b;
			
		/*} catch (ArrayIndexOutOfBoundsException e) {
			arr = new int[2];
			arr[1] = 1;
		}*/
		/*throw new ArrayIndexOutOfBoundsException();*/
		/*return a1.b.b;*/
	}


	/**
	 * @return
	 */
	public boolean empty() {
		// TODO Auto-generated method stub
		return false;
	}


	/**
	 * @return
	 */
	public JavaClass dequeue() {
		// TODO Auto-generated method stub
		return null;
	}


	/**
	 * @param a
	 */
	public void enqueue(A a) {
		// TODO Auto-generated method stub
		
	}



	

		
				//	
	////
	//// public void testLoop() {
	//// int k = 10;
	//// for (int i = 0; i < 5; i++) {
	//// a = new Code();
	//// do {
	//// do {
	//// k++;
	//// if ( a == null) {
	//// return;
	//// }
	//// } while ( k < 100);
	//// i ++;
	//// for (int p = 200 ; p >100; p--) {
	//// p = p*2;
	//// }
	//// for ( int s = 0; s< 100; s++) {
	//// while ( s <10 ) {
	//// if (s == 5) {
	//// break;
	//// }
	//// s--;
	//// }
	//// s = s + 1;
	//// }
	//// } while ( i < 10);
	//// }
	//// }
	////
	//		  /*
	//		   * @ensures result == this;
	//		   */
	//		public A TestBranch(A a1, A a2) {
	//			if (j == 5) {
	//				a2 = this;
	//				return a2;
	//			} else {
	//// a2.b.b = a1;
	//
	//				a2.b = a1;
	//				a1 = this;
	//				return a2.b ;
	//			}
	//		}
	//	/**
	//	 * requires arr != null;
	//	 */
	//	  public void arrayaccess() {
	//		long z =0;
	//
	//		  for (int i = 0; i < 30; i++ ) {
	//			  int k = 0;
	//			  do {
	//				  A a = new A();
	//				  if ( k == 5) {
	//					  for (int s = 0; s < 20; s++) {
	//						  A a = new A();
	//						  a.j = s;
	//					  }
	//					  continue;
	//				  }
	//				  k++;
	//		  		} while(k < 10) ;
	//			
	//			  arr[0] = arr[i] + 1;
	//			  while ( i > 10 && i <15) {
	//			
	//				  arr[i] = arr[i] + 1;
	//				  if ( i == 11) {
	//					  continue;
	//				  }
	//				  i++;
	//			  }
	//		  }
	//	  }
}