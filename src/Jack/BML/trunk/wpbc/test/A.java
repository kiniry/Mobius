package test;

public class A {
		
        
		/*
		 * @ requires i == 1;
		 * @ ensures \result == i;
		 *
		 **/
		public int m(int i) {
				return i;
		} 
        
		/*
		 * @ ensures \result > 0
		 */
		public int n(){
				return m(1);
		}
}