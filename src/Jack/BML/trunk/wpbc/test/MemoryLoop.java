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
public class MemoryLoop {
	
	
	 int memory;
	 int memoryBeforeLoop;
	 
	 void loop() {
	 	int i= 0;
	 	memory = 2;
	 	memoryBeforeLoop = 2;
	
	 	//@ loop_modifies memory, i;
		//@ loop_invariant  (memory <= memoryBeforeLoop + 4*i) && i <= 3;
	 	while ( i <  3) {
	 		memory = memory  + 4;
	 		new A();
	 		new A();
	 		new A();
	 		i++;
	 		
		 	while ( i <  3) {
		 		memory = memory  + 4;
		 		new A();
		 		new A();
		 		new A();
		 		i++;
		 	}
	 	}
	 	

	 	
	 	while ( i <  3) {
	 		memory = memory  + 4; 	
	 		A a1 = new A();//1
	 		A a2 = new A();//1
	 		if ( i == 0) {
	 			break;
	 		}
	 		(new A()).modifyArray();// 2
	 		(new A()).testThisAccess(a1, a2);//6
	 		
	 		i++;
	 	}
	 	
	 
	 }

}
