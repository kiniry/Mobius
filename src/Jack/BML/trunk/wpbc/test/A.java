package test;

public class A {
	public A b;

	public int j;

	public final static int CONST = 210;

	//	public static Code a = new Code();

	public int arr[] = new int[5];

	public A[] array = new A[3];

	/*
	 * @ensures \result == b;
	 */
	public A testMethodInvokation() throws NullPointerException {
		b = b.testThisAccess(b, b);
		return b;
	}

	//@ requires true;
	//@ modifies b, a1; 
	//@ ensures \result == this;
	//@  exsures (ArrayIndexOutOfBoundsException e) arr.length < 2;

	public A testThisAccess(A a1, A a2) {
		//		try {
		a1.b.b = this;
		b = a1.b.b;
		arr[1] = 1;
		//			throw new ArrayIndexOutOfBoundsException();
		//			return b;
		//		} catch (ArrayIndexOutOfBoundsException e) {
		//			arr = new int[2];
		//			arr[1]= 1;
		//		}
		return a1.b.b;
	}

	/**
	 *  i mod k = 
	 * if i < k then i
	 * if i == k then 0
	 * if i > k  then mod((i - k), k)  
	 */


	/*
	 * this = loc(0)
	 * i = loc(1)
	 * k = loc(2)
	 * constant = loc(3)
	 * s = loc( 4 )
	 */
	/*
	 *@ ensures \result == i % k;
	 */
	public int mod(int i, int k) {
		int constant = i;
		/*@
		  loop_modifies i, s;
		  loop_invariant  constant == s * k + i ;
		 */
		for (int s = 0; true; s++) {
			if (i <= k) {
				break;
			}
			i = i - k; // loc(1) = loc(1) - loc( 2 )
		}

		if (i == k) {
			return 0;
		}
		return i;
	}

	//	
	////	
	////	public void testLoop() {
	////	int k = 10;
	////		for (int i = 0; i < 5; i++) {
	////			a = new Code();
	////			do {
	////				do {
	////					k++;
	////					if ( a == null) {
	////						return;
	////					}
	////				} while ( k < 100);
	////				i ++;
	////				for (int p = 200 ; p >100; p--) {
	////					p = p*2;
	////				}
	////				for ( int s = 0; s< 100; s++) {
	////					while ( s <10 ) {
	////						if (s == 5) {
	////							break;
	////						}
	////						s--;
	////					}
	////					s = s + 1;
	////				}
	////			} while ( i < 10);
	////		}	
	////	}
	////	
	//		  /*
	//		   * @ensures result == this;
	//		   */
	//		public A TestBranch(A a1, A a2) {
	//			if (j == 5) {
	//				a2 = this;
	//				return a2;
	//			} else {
	////				a2.b.b = a1;
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
	//		  for (int i = 0; i  < 30; i++ ) {
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
	//			  while ( i > 10  &&  i <15) {
	//			
	//				  arr[i] = arr[i] + 1;
	//				  if ( i == 11) {
	//					  continue;
	//				  }
	//				  i++;
	//			  }
	//		  }
	//	  }

	//	/*
	//	   * @ensures result == j;
	//	   */
	//	public int TestReferenceSubstitution(A a1, A a2) {
	//		b.b.j = 5;
	//		a1.j = 2;
	//		a2.j = 3;
	//		return a2.j;
	//	}
	//	/*
	//	 * @ensures result == 2
	//	 */
	//	public int TEST() {
	//		j = 2;
	//		return j;
	//	}
	//
	//	/*
	//	 * @ requires j > 0;
	//	 * @modifies j;
	//	 * @ ensures \result == j;
	//	 **/
	//	public int m() {
	//		return 2;
	//	}
	//
	//	/*
	//	 * @ ensures \result > 0
	//	 */
	//	public int n() {
	//		/*A a = new A();
	//		a.m(1);*/
	//		return m();
	//
	//	}

	//	public A[] getArray() {
	//		return array;
	//	}
	//
	//	public void testString() {
	//		String s1 = "abc";
	//		String s2 = null;
	//
	//		try {
	//			s2 = "a";
	//			s1.substring(0);
	//			/*throw new NullPointerException();*/
	//		} catch (NullPointerException _e) {
	//			_e.getMessage();
	//		}
	//		s1 = s2;
	//		j = 3;
	//	}

}