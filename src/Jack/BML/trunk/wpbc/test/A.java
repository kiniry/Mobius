package test;

public class A {
		
        public static long i;
        
        public static Code a = new Code();
		
		/*
		 * ignore @ requires i == 1;
		 * @ ensures \result == i;
		 *
		 **/ 
		public static  long m() {
				//i++;
				a.toString();
				return i;
				
		} 
        
		/*
		 * @ ensures \result > 0
		 */
		public long n(){
				return m();
		}
		
		
		
}