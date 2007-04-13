
public class Super {

	boolean i;
	
	
	//invariant i > 0; 
	
	//public behavior
	//  requires x > 0;
	//  requires i == 1;
	//  ensures i == 1;
	//  ensures \result > 0;
	//@  requires i ==> x;
	public boolean f(boolean x){
		return x;
	}
	
}

//public class Sub extends Super {
//
//	//@also public behavior
//	//@  requires x > -2;
//	//@  ensures \result > 2;
//	public int f(int x){
//		
//	}
//	
//}