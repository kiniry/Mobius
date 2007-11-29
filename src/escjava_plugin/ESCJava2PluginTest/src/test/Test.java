package test;

public class Test {
	
	//@ requires x > 2;
	//@ ensures \result != x;
	private int test (int x) {
		//@ assert false;
		return x;
		
	}
	
	public void main() {
		test (1);
		test (2);
		test (3);
	}
	
	
	public static class InnerClass {
		
		
		int y;
		
		
		public static class InnerMostClass {
			
		}
		
	}

}
