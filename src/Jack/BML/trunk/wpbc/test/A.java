package test;

public class A {
	public A b;

	public int j;

	public final static int CONST = 210;

	public static Code a = new Code();

	public int arr[] = new int[5];

	public A[] array = new A[3];


	/*
	* @ensures result == this;
	*/
	public A TestThisAccess(A a1)  {
		a1.b = this;
		b= a1;
		return b;
	}

	/*
	   * @ensures result == j;
	   */
	public A TestBranch(A a1, A a2) {
		if (b.b.j == 5) {
			a2 = this;
			return a2.b;
		} else {
			a2.b = a1;
			return a2;
		}
	}


	/*
	   * @ensures result == j;
	   */
	public int TestReferenceSubstitution(A a1, A a2) {
		b.b.j = 5;
		a1.j = 2;
		a2.j = 3;
		return a2.j;
	}
	/*
	 * @ensures result == 2
	 */
	public int TEST() {
		j = 2;
		return j;
	}

	/*
	 * @ requires j > 0;
	 * @modifies j;
	 * @ ensures \result == j;
	 **/
	public int m() {
		return 2;
	}

	/*
	 * @ ensures \result > 0
	 */
	public int n() {
		/*A a = new A();
		a.m(1);*/
		return m();

	}

	//requires arr != null
	public void arrayaccess() {
		arr[0] = arr[1] + 1;
	}

	public A[] getArray() {
		return array;
	}

	public void testString() {
		String s1 = "abc";
		String s2 = null;

		try {
			s2 = "a";
			s1.substring(0);
			/*throw new NullPointerException();*/
		} catch (NullPointerException _e) {
			_e.getMessage();
		}
		s1 = s2;
		j = 3;
	}

}