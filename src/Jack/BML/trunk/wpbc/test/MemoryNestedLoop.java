/*
 * Created on Feb 11, 2005
 *
 * TODO To change the template for this generated file go to
 * Window - Preferences - Java - Code Style - Code Templates
 */
package test;

/**
 * @author mpavlova
 *
 * TODO To change the template for this generated type comment go to
 * Window - Preferences - Java - Code Style - Code Templates
 */
public class MemoryNestedLoop {


	 int memory;
	 int memoryBeforeLoop;
	 
	 
	 void loopssssssssss() {
	 	(new B(5,5 ) ).m2(); // 2 mem units
	 	for ( int k = 0; k < 100 ; k++) {
	 	int i= 0;

	 	new A();
	 	new A();
	 	(new B(3,3 )).m2(); // 5 mem units
	 	for (int s = 0; s < 2 ; s++) {
	 		new A();
	 		new A(); //2 units
	 		do {
	 			new A(); // 1 
	 		
	 		} while(s < 7);
	 		for ( s = 0 ; s < 7;s --) {
	 			new A();
		 		new A();
		 		new A();
		 		new A();
		 		new A();
		 		new A(); // 6
	 		}
	 	}
	 	//@ loop_modifies memory, i;
		//@ loop_invariant  ( memory  <= memoryBeforeLoop + i*(4 + 3*2 )) && i <= 3;
	 	while ( i <  3) {
	 		memory = memory  + 4;
	 		  new A();
	 		new A();
	 		new A();
	 		 new A(); // 4
	 		int j = 0;
	 		//@ loop_modifies memory, j;
			//@ loop_invariant  (memory <= memoryBeforeLoop + i*( 4 + 3*2 ) + 4  + j*2) && j <= 2;
	 		while ( j < 2) {
	 			new A();
		 		new A();// 2
	 			memory = memory + 2;
	 			j++;
	 		}
	 		i++;
	 	
	 	}
	 	
	 	new A(); // 1
	 	}
	 }

}
