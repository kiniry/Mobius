/*
 * Created on Feb 17, 2005
 *
 * TODO To change the template for this generated file go to
 * Window - Preferences - Java - Code Style - Code Templates
 */
package test;

/**
 * @author mpavlova
 * 
 * TODO To change the template for this generated type comment go to Window -
 * Preferences - Java - Code Style - Code Templates
 */
public class MoreNestedLoops {

		 int memory;
		 int memoryBeforeLoop;
		 
		 B b;
		 void loop() {
		 	int i =0;
		 	while ( i <  3) {//32 num 0
		 		int j = 0;
		 		while ( j < 2) { //37 num 1
		 			j++;
		 			while ( j > 3) {//2
		 				j--;
		 				
		 				while ( j > 3) {//3
			 				j--;
			 				do { //4
			 					j++;
			 					new A();
			 				}while ( j != 0);
			 			}
			 			}
		 			
		 		}
		 		i++;
		 	}
		 	int k = 0;
		 	while (k < 5 ) { //45   num 5
		 		b.m2();
 				memory = memory + 3;
 				
 				do { // 49 num 6
 					k--;
 				}while ( k < 10 );
 				k++;
 			}
		 }

	}
