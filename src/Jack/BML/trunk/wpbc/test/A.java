package test;

public class A  {
		
        public int j;
        
        public final static  int CONST  = 210;
        
        public static Code a = new Code();
        
        public int arr[] = new int[5];
		
        public A[] array = new A[3];
		/*
		 * @ requires j > 0;
		 * @modifies j;
		 * @ ensures \result == j;
		 **/ 
		public   int m()  {
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
		
		
		public A[] getArray( ) {
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